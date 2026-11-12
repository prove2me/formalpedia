-- Prove2me | solution 1 for IsotropicSpin.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T23:36:50.845197+00:00
-- url     : https://prove2.me/submissions/668edf38-702f-4308-b328-478968abd744

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

open scoped Matrix
open Matrix Polynomial

private lemma q2_entropy_sum {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    WHAdditivity.Renyi.vonNeumannEntropy H =
      ∑ i, Real.negMulLog (hH.eigenvalues i) := by
  unfold WHAdditivity.Renyi.vonNeumannEntropy
  rw [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal,
    Function.comp_apply]
  simp

private lemma q2_entropy_roots {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (p : ℕ) :
    ((X ^ p * H.charpoly).roots.map (fun z : ℂ => Real.negMulLog z.re)).sum =
      WHAdditivity.Renyi.vonNeumannEntropy H := by
  rw [q2_entropy_sum H hH,
    roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (Matrix.charpoly_monic H).ne_zero),
    roots_X_pow, hH.roots_charpoly_eq_eigenvalues]
  simp [Multiset.map_nsmul, Multiset.sum_nsmul]

private lemma q2_entropy_gram {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) :
    WHAdditivity.Renyi.vonNeumannEntropy (A * Aᴴ) =
      WHAdditivity.Renyi.vonNeumannEntropy ((Aᴴ * A)ᵀ) := by
  have h1 := Matrix.isHermitian_mul_conjTranspose_self A
  have h2 := Matrix.isHermitian_conjTranspose_mul_self A
  rw [← q2_entropy_roots _ h1 (Fintype.card n),
    ← q2_entropy_roots _ h2.transpose (Fintype.card m),
    Matrix.charpoly_transpose, Matrix.charpoly_mul_comm']




/-- **Pure-input output entropy equals the entropy of `Ω`**, Alicki, arXiv:quant-ph/0402080v1,
eq. (15), p. 2 (cited there from [2]): for a channel `Λ(ρ) = Σ_k X_k ρ X_k†` and a vector `φ`,
`S(Λ(|φ⟩⟨φ|)) = S(Ω)` with `Ω_{kl} = ⟨φ, X_l† X_k φ⟩`.

**Formalization Note** Stated for every finite family of operators `X : κ → Matrix ι ι ℂ` and every
vector `φ` (no trace preservation and no normalization of `φ` is needed). The page writes
`Ω_{kl} = ⟨φ, X_l X_k φ⟩`, where the `X_k` are the Hermitian Kraus operators `S_k/√(s(s+1))` of
(6); for Hermitian `X_l` this is `⟨φ, X_l† X_k φ⟩`. `S` is the von Neumann entropy of the
published bundle `WHAdditivity.Renyi` (natural logarithm). -/
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : κ → Matrix ι ι ℂ) (φ : ι → ℂ) :
    WHAdditivity.Renyi.vonNeumannEntropy (∑ k, X k * WHAdditivity.Renyi.pureState φ * (X k)ᴴ) =
      WHAdditivity.Renyi.vonNeumannEntropy
        (Matrix.of fun k l => star φ ⬝ᵥ (((X l)ᴴ * X k) *ᵥ φ)) := by
  classical
  let W : Matrix ι κ ℂ := fun i k => (X k *ᵥ φ) i
  have hL : (∑ k, X k * WHAdditivity.Renyi.pureState φ * (X k)ᴴ) = W * Wᴴ := by
    simp only [WHAdditivity.Renyi.pureState, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
    ext i j
    change (∑ k, Matrix.vecMulVec (X k *ᵥ φ) (star (X k *ᵥ φ))) i j =
      ∑ k, (X k *ᵥ φ) i * star ((X k *ᵥ φ) j)
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  have hR : (Matrix.of fun k l => star φ ⬝ᵥ (((X l)ᴴ * X k) *ᵥ φ)) = (Wᴴ * W)ᵀ := by
    ext k l
    change star φ ⬝ᵥ (((X l)ᴴ * X k) *ᵥ φ) = (Wᴴ * W) l k
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_conjTranspose, star_star]
    rfl
  rw [hL, hR]
  exact q2_entropy_gram W
