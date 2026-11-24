-- Prove2me | solution 1 for GlobalTheory.WittGauss.pow_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:54.877813+00:00
-- url     : https://prove2.me/submissions/ff2c6d10-7834-4b17-be6c-33f854518acd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittGauss
open WittVector
namespace GlobalTheory.WittGauss
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (t ^ p ^ n) ^ ((1 : ℝ) / (p : ℝ) ^ n) = t := by
  rw [one_div, ← Nat.cast_pow]
  exact Real.pow_rpow_inv_natCast ht (pow_ne_zero _ hp.out.ne_zero)
end GlobalTheory.WittGauss
