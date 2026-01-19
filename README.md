# Sherman-Morrison Theorem in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18283772.svg)](https://doi.org/10.5281/zenodo.18283772)

[![Lean CI](https://github.com/kaneplusplus/ShermanMorrison/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/kaneplusplus/ShermanMorrison/actions/workflows/lean-ci.yml)

A complete formal verification of the Sherman-Morrison theorem in Lean 4 with Mathlib. This theorem provides an efficient formula for computing the inverse of a rank-one update to an invertible matrix, which is fundamental in numerical linear algebra, optimization algorithms, and statistical computing.

## Authors

- **Michael J. Kane** <michael.kane@r-project.org>
  [ORCID: 0000-0003-1899-6662](https://orcid.org/0000-0003-1899-6662)

- **Aristotle (Harmonic)** <aristotle-harmonic@harmonic.fun>

- **Daniel Zelterman** <daniel.zelterman@yale.edu>
  [ORCID: 0000-0003-0711-8688](https://orcid.org/0000-0003-0711-8688)


**BibTeX:**
```bibtex
@software{sherman_morrison_lean4_2026,
  author       = {Kane, Michael J. and
                  Aristotle (Harmonic) and
                  Zelterman, Daniel},
  title        = {Sherman-Morrison Theorem: Formal Verification in Lean 4},
  year         = {2026},
  publisher    = {Zenodo},
  version      = {0.1.0},
  doi          = {10.5281/zenodo.18283772},
  url          = {https://doi.org/10.5281/zenodo.18283772}
}
```

For detailed citation information, see [CITATION.cff](CITATION.cff).


## Theorem Statement

Given an invertible matrix $A \in \mathbb{R}^{n \times n}$ and column vectors $u, v \in \mathbb{R}^n$, the matrix $(A + uv^T)$ is invertible if and only if $(1 + v^T A^{-1} u) \neq 0$, and in that case:

$$(A + uv^T)^{-1} = A^{-1} - \frac{A^{-1}uv^T A^{-1}}{1 + v^T A^{-1} u}$$

## Key Definitions

### Outer Product Matrix
The term $uv^T$ represents the **outer product** of vectors $u$ and $v$:

$$(uv^T)_{ij} = u_i \cdot v_j$$

This is a rank-1 matrix (or rank-0 if either vector is zero).

### Sherman-Morrison Scalar
The scalar $\alpha = 1 + v^T A^{-1} u$ appears in the denominator. Expanding this:

$$\alpha = 1 + \sum_{i=1}^{n} v_i (A^{-1}u)_i = 1 + v^T A^{-1} u$$

This scalar determines whether the rank-1 update preserves invertibility.

## Proof Strategy

The proof works by **verifying the inverse directly**: we show that the proposed inverse formula actually satisfies the defining property of a matrix inverse.

Specifically, we prove:

$$(A + uv^T) \cdot \left(A^{-1} - \frac{A^{-1}uv^T A^{-1}}{1 + v^T A^{-1} u}\right) = I$$

### Step 1: Expand the Product

Let $B = A + uv^T$ and let $\alpha = 1 + v^T A^{-1} u$. We want to show:

$$B \cdot \left(A^{-1} - \frac{1}{\alpha} A^{-1}uv^T A^{-1}\right) = I$$

Expanding the left side using distributivity:

$$B \cdot A^{-1} - \frac{1}{\alpha} B \cdot A^{-1}uv^T A^{-1}$$

### Step 2: Substitute $B = A + uv^T$

For the first term:
$$(A + uv^T) \cdot A^{-1} = A A^{-1} + uv^T A^{-1} = I + uv^T A^{-1}$$

For the second term:
$$(A + uv^T) \cdot A^{-1}uv^T A^{-1} = A A^{-1}uv^T A^{-1} + uv^T A^{-1}uv^T A^{-1}$$
$$= uv^T A^{-1} + uv^T A^{-1}uv^T A^{-1}$$

### Step 3: Factor Out Common Terms

The second term becomes:
$$uv^T A^{-1}(I + uv^T A^{-1})$$

Using the associativity of matrix multiplication and the fact that $v^T A^{-1}u$ is a scalar:
$$uv^T A^{-1} + u(v^T A^{-1}u)v^T A^{-1}$$

### Step 4: Apply the Scalar Identity

The key observation is that $v^T A^{-1}u$ is a scalar, so:
$$u(v^T A^{-1}u)v^T A^{-1} = (v^T A^{-1}u) \cdot uv^T A^{-1}$$

Therefore, the second term of our original expansion is:
$$\frac{1}{\alpha}[uv^T A^{-1} + (v^T A^{-1}u) \cdot uv^T A^{-1}]$$
$$= \frac{1}{\alpha} \cdot uv^T A^{-1}(1 + v^T A^{-1}u)$$
$$= \frac{1}{\alpha} \cdot uv^T A^{-1} \cdot \alpha$$
$$= uv^T A^{-1}$$

### Step 5: Combine and Cancel

Putting it all together:
$$(A + uv^T) \cdot \left(A^{-1} - \frac{1}{\alpha} A^{-1}uv^T A^{-1}\right)$$
$$= I + uv^T A^{-1} - uv^T A^{-1}$$
$$= I$$

The $uv^T A^{-1}$ terms cancel perfectly! This is the magic of the Sherman-Morrison formula.

## Why the Condition $1 + v^T A^{-1}u \neq 0$?

The condition $\alpha = 1 + v^T A^{-1}u \neq 0$ is necessary because:

1. We divide by $\alpha$ in the formula, so $\alpha = 0$ would make the formula undefined
2. Geometrically, when $\alpha = 0$, the rank-1 update $uv^T$ exactly cancels an eigenspace of $A$, making $A + uv^T$ singular

## Lean Proof Structure

The Lean formalization follows this outline:

### 1. Setup Phase (lines 40-43)
Define the key expressions:
- `uv_outer`: The matrix $uv^T$
- `vt_Ainv_u`: The scalar $v^T A^{-1}u$

### 2. Main Lemma (lines 47-70)
Prove that $(A + uv^T) \cdot \text{(proposed inverse)} = I$ by case analysis on whether $A^{-1}$ exists.

**Case 1** (lines 56-62): $A$ is invertible
- Expand the matrix product element-by-element
- Use field simplification (`field_simp`) to clear denominators
- Apply ring normalization (`ring_nf`) to simplify algebraic expressions
- Finish with matrix and sum manipulations

**Case 2** (lines 64-70): $A^{-1} = 0$ (contradiction case)
- This case is vacuous because $A$ is assumed invertible
- Show that $A^{-1} = 0$ contradicts $\det(A) \neq 0$
- Handle edge cases for empty or singleton dimensions

### 3. Conclusion (lines 73-88)
From the main lemma `h_inv`:
- Derive the inverse equality using `Matrix.inv_eq_right_inv`
- Prove $\det(A + uv^T) \neq 0$ using the fact that it has a right inverse
- Show the formula matches the required form by simplifying the matrix expressions

## Computational Significance

The Sherman-Morrison formula is computationally important because:

1. **Efficiency**: Computing $(A + uv^T)^{-1}$ directly requires $O(n^3)$ operations
2. **Using the formula**: If $A^{-1}$ is already known, computing $(A + uv^T)^{-1}$ requires only $O(n^2)$ operations
3. **Applications**: Frequently used in optimization, statistics (Kalman filters), and numerical linear algebra

## Generalization

This formula generalizes to the **Woodbury matrix identity** for rank-$k$ updates:

$$(A + UCV)^{-1} = A^{-1} - A^{-1}U(C^{-1} + VA^{-1}U)^{-1}VA^{-1}$$

where $U, V \in \mathbb{R}^{n \times k}$ and $C \in \mathbb{R}^{k \times k}$.

The Sherman-Morrison formula is the special case where $k = 1$, $U = u$, $V = v^T$, and $C = 1$.

---

## Dependencies

- **Lean version**: `leanprover/lean4:v4.24.0`
- **Mathlib commit**: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

### Mathlib Libraries Used
The proof imports and uses:
- `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` - Matrix inverse theory
- `Mathlib.Data.Matrix.Basic` - Basic matrix operations
- `Mathlib.Tactic.FieldSimp` - Field simplification tactics

## Installation and Building

### Prerequisites

1. Install Lean 4 using [elan](https://github.com/leanprover/elan):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. Ensure you have Git installed for fetching dependencies.

### Building the Project

```bash
# Clone or download this repository
cd ShermanMorrison

# Build the project (this will download Mathlib and compile everything)
lake build

# Verify the theorem
lean ShermanMorrison.lean
```

The build process will:
1. Download and cache the specified version of Mathlib
2. Compile all dependencies
3. Verify the Sherman-Morrison proof

**First build time**: 5-30 minutes depending on your system and whether Mathlib cache is available.
**Subsequent builds**: Under 1 minute.

## Verification

To verify the proof is correct:

```bash
# Build and check all proofs
lake build

# Type-check the theorem directly
lean ShermanMorrison.lean
```

All proofs are constructive and verified by the Lean 4 type checker.

## Project Structure

```
.
├── README.md                  # This file
├── ShermanMorrison.lean       # Main theorem proof
├── lakefile.toml              # Lake build configuration
├── lean-toolchain             # Specifies Lean version
├── CITATION.cff               # Citation metadata
├── LICENSE                    # MIT License
└── .zenodo.json               # Zenodo metadata
```

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## References

1. Sherman, J., & Morrison, W. J. (1950). Adjustment of an inverse matrix corresponding to a change in one element of a given matrix. *The Annals of Mathematical Statistics*, 21(1), 124-127. [DOI: 10.1214/aoms/1177729893](https://doi.org/10.1214/aoms/1177729893)

2. The Lean 4 Theorem Prover: https://leanprover.github.io/

3. Mathlib4 Documentation: https://leanprover-community.github.io/mathlib4_docs/

4. Woodbury Matrix Identity: Woodbury, M. A. (1950). Inverting modified matrices. *Memorandum Report 42*, Statistical Research Group, Princeton University.

## Acknowledgments

This proof was developed with assistance from **Aristotle**, an AI proof assistant by Harmonic (https://harmonic.fun/).

**Project UUID**: `72000105-cc0a-45d1-a3d9-9c2c76ac72d6`

---

*For questions or contributions, please contact the authors.*
