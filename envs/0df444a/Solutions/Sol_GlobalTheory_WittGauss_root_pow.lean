-- Prove2me | solution 1 for GlobalTheory.WittGauss.root_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:38.415658+00:00
-- url     : https://prove2.me/submissions/fb5464d3-4dca-4bf8-bacb-ec53dab41774

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
    (t ^ ((1 : ℝ) / (p : ℝ) ^ n)) ^ p ^ n = t := by
  rw [one_div, ← Nat.cast_pow]
  exact Real.rpow_inv_natCast_pow ht (pow_ne_zero _ hp.out.ne_zero)
end GlobalTheory.WittGauss
