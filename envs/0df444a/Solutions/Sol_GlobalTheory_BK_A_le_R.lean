-- Prove2me | solution 1 for GlobalTheory.BK.A_le_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:04.796531+00:00
-- url     : https://prove2.me/submissions/3f01988e-bfb5-4443-883f-312372e20a5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_rad_nonneg
import Theorems.Thm_GlobalTheory_BK_mem_R
import Theorems.Thm_GlobalTheory_BK_rad_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 < k) : A O K ≤ R O K l k := fun f hf =>
  mem_R.2 <| squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k) n))
    (fun n => mul_le_of_le_one_left (pow_nonneg (rad_nonneg l k) n) (hf n))
    (tendsto_pow_atTop_nhds_zero_of_lt_one (rad_nonneg l k) (rad_lt_one l hk))
end GlobalTheory.BK
