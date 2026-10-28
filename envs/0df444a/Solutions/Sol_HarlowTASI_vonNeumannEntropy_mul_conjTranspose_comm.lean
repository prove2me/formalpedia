-- Prove2me | solution 1 for HarlowTASI.vonNeumannEntropy_mul_conjTranspose_comm
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-26T20:35:11.01437+00:00
-- url     : https://prove2.me/submissions/a9f77dd9-63b7-4d73-ac0c-792cc0ffcb95

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

open Matrix Polynomial

namespace HarlowTASI

/-- For Hermitian `H`, summing `negMulLog ∘ re` over the roots of `X ^ p * charpoly H` gives the
entropy sum over the eigenvalues: the extra roots are `0` and `negMulLog 0 = 0`. -/
lemma vnc_roots_sum {k : Type} [Fintype k] [DecidableEq k] (H : Matrix k k ℂ)
    (hH : H.IsHermitian) (p : ℕ) :
    ((X ^ p * H.charpoly).roots.map (fun z : ℂ => Real.negMulLog z.re)).sum =
      ∑ i, Real.negMulLog (hH.eigenvalues i) := by
  rw [roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (Matrix.charpoly_monic H).ne_zero),
    roots_X_pow, hH.roots_charpoly_eq_eigenvalues]
  simp [Multiset.map_nsmul, Multiset.sum_nsmul]

end HarlowTASI

open HarlowTASI

/-- `AA†` and `A†A` have the same nonzero eigenvalues with multiplicity
(`X^|n| χ_{AA†} = X^|m| χ_{A†A}`), so their entropies agree. -/
theorem solution {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) :
    vonNeumannEntropy (A * Aᴴ) = vonNeumannEntropy (Aᴴ * A) := by
  have h1 := isHermitian_mul_conjTranspose_self A
  have h2 := isHermitian_conjTranspose_mul_self A
  unfold vonNeumannEntropy
  rw [dif_pos h1, dif_pos h2, ← vnc_roots_sum _ h1 (Fintype.card n),
    ← vnc_roots_sum _ h2 (Fintype.card m), charpoly_mul_comm']
