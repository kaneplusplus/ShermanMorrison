/-
Sherman-Morrison Theorem - Formal Proof in Lean 4
==================================================

Authors:
--------
Author: Michael J. Kane <michael.kane@r-project.org> (ORCID: 0000-0003-1899-6662)
Co-author: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
Co-author: Daniel Zelterman <daniel.zelterman@yale.edu> (ORCID: 0000-0003-0711-8688)

Technical Details:
------------------
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
Project UUID: 72000105-cc0a-45d1-a3d9-9c2c76ac72d6

This file was created with assistance from Aristotle, an AI proof assistant,
to formally verify the Sherman-Morrison theorem in Lean 4.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FieldSimp

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {R : Type*} [Field R]

/-- The Sherman-Morrison theorem: Given an invertible matrix A and column vectors u and v,
    the matrix (A + uvᵀ) is invertible if and only if (1 + vᵀA⁻¹u) ≠ 0, and in that case:
    (A + uvᵀ)⁻¹ = A⁻¹ - (A⁻¹uvᵀA⁻¹)/(1 + vᵀA⁻¹u) -/
theorem sherman_morrison
  (A : Matrix n n R) (u v : n → R)
  (hA : IsUnit A.det)
  (h : 1 + (∑ i, v i * (A⁻¹.mulVec u) i) ≠ 0) :
  let B := A + of (fun i j => u i * v j)
  IsUnit B.det ∧
  B⁻¹ = A⁻¹ - (1 + (∑ i, v i * (A⁻¹.mulVec u) i))⁻¹ •
    of (fun i j => (∑ k, A⁻¹ i k * u k) * (∑ l, v l * A⁻¹ l j)) := by
  -- Define the outer product matrix uv^T
  set uv_outer := Matrix.of (fun i j => u i * v j) with huv_outer

  -- Define the scalar v^T A^{-1} u (appears in denominator)
  set vt_Ainv_u := ∑ i, v i * (A⁻¹.mulVec u) i with hvt_Ainv_u

  -- The key step: show that (A + uv^T) times the proposed inverse equals I
  -- Proposed inverse: A^{-1} - (1/(1 + v^T A^{-1} u)) • (A^{-1} uv^T A^{-1})
  have h_inv : (A + uv_outer) *
               (A⁻¹ - (1 / (1 + vt_Ainv_u)) • (A⁻¹ * uv_outer * A⁻¹)) = 1 := by
    rcases Matrix.nonsing_inv_cancel_or_zero A with (hA' | hA')
      <;> simp_all +decide [Matrix.mul_assoc, mul_sub]

    -- Case 1: A is invertible (A * A⁻¹ = 1)
    -- Expand (A + uv^T)(A⁻¹ - scale • A⁻¹ uv^T A⁻¹)
    -- This gives: I + uv^T A⁻¹ - scale • A⁻¹ uv^T - scale • uv^T A⁻¹ uv^T A⁻¹
    -- The middle terms cancel due to the specific choice of scale factor
    · ext i j
      simp +decide [Matrix.mul_apply, add_mul, mul_assoc, hA]
      -- Field arithmetic and ring simplification needed here
      -- Combine like terms and simplify the expression.
      field_simp [h]
      ring_nf
      simp +decide [ Matrix.mulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]

    -- Case 2: A⁻¹ = 0 (this contradicts hA: A is invertible)
    · -- If A is invertible, then A⁻¹ * A = 1
      -- But if A⁻¹ = 0, then 0 * A = 1, giving 0 = 1 (contradiction)
      replace hA' := congr_arg Matrix.det hA'
      simp_all +decide
      cases isEmpty_or_nonempty n <;> simp_all +decide
      exact Subsingleton.elim _ _

  -- From the right inverse h_inv, we can conclude both parts of the theorem

  -- Since (A + uv^T) * proposed_inv = I, the proposed inverse is the actual inverse
  have h_inv_eq : (A + uv_outer)⁻¹ =
                  A⁻¹ - (1 / (1 + vt_Ainv_u)) • (A⁻¹ * uv_outer * A⁻¹) := by
    rw [Matrix.inv_eq_right_inv h_inv]

  -- Simplify let-bound variables to match the goal
  simp +zetaDelta at *

  -- Now prove both parts: IsUnit B.det and the inverse formula
  -- Since the determinant is zero if and only if the matrix is not invertible, and we have h_inv which shows that (A + uv_outer) * (A⁻¹ - ...) = 1, it follows that the determinant of (A + uv_outer) is non-zero.
  have h_det : (A + (Matrix.of fun i j => u i * v j)).det ≠ 0 := by
    exact fun h => by simpa [ h ] using congr_arg Matrix.det h_inv;
  -- By definition of matrix multiplication and scalar multiplication, the two matrices are equal.
  simp [h_inv_eq] at *;
  exact ⟨ h_det, by ext i j; simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ⟩
