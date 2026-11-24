-- Prove2me | solution 1 for GlobalTheory.IsoIdem.eq_zero_of_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:12.173447+00:00
-- url     : https://prove2.me/submissions/da4c328e-1f08-44eb-96bf-14edecd4389a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsotropicIdempotentCentralizerHermitian
import Theorems.Thm_GlobalTheory_CommSep_eq_aeval_of_commute_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.IsoIdem
namespace GlobalTheory.IsoIdem
theorem _root_.solution {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hs : A.charpoly.Separable) (y : Matrix (Fin r) (Fin r) E) (hy : y * A = A * y) (k : ℕ)
    (hk : y ^ k = 0) : y = 0 := by
  obtain ⟨q, rfl⟩ := GlobalTheory.CommSep.eq_aeval_of_commute_of_separable A hs y hy
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact eq_zero_of_zero_eq_one hk.symm _
  have hsq : Squarefree (minpoly E A) :=
    Squarefree.squarefree_of_dvd (Matrix.minpoly_dvd_charpoly A) hs.squarefree
  have h1 : minpoly E A ∣ q ^ (k + 1) := minpoly.dvd E A (by rw [map_pow]; exact hk)
  have h2 : minpoly E A ∣ q := (hsq.dvd_pow_iff_dvd (by omega)).1 h1
  exact minpoly.dvd_iff.1 h2
end GlobalTheory.IsoIdem
