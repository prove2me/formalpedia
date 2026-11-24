-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.fac_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:52:08.707841+00:00
-- url     : https://prove2.me/submissions/0b1e39fb-bac1-41a4-a0df-c4d0f4880590

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
import Theorems.Thm_GlobalTheory_TriangularityLowCoeff_expOf_apply_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TriangularityLowCoeff
open MvPolynomial
namespace GlobalTheory.TriangularityLowCoeff
theorem _root_.solution {d : ℕ} (L : List (Fin d)) : fac L 0 ∣ (L.length).factorial ^ L.length := by
  induction L with
  | nil => simp [fac]
  | cons i L ih =>
    simp only [fac, zero_add, List.length_cons]
    rw [pow_succ']
    refine mul_dvd_mul (Nat.dvd_factorial (by omega) (by have := expOf_apply_le L i; omega)) ?_
    exact ih.trans (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (by omega)) _)
end GlobalTheory.TriangularityLowCoeff
