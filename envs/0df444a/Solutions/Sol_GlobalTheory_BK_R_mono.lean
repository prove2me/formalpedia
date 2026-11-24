-- Prove2me | solution 1 for GlobalTheory.BK.R_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:00:09.082374+00:00
-- url     : https://prove2.me/submissions/f3201e22-d263-4f4a-b1c3-8ccf27b03682

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_rad_nonneg
import Theorems.Thm_GlobalTheory_BK_mem_R

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] {k k' : ℝ} (h : k ≤ k') : R O K l k ≤ R O K l k' := fun f hf =>
  mem_R.2 <| squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k') n))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (rad_nonneg l k')
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Fact.out : l.Prime).one_le)
        (by linarith)) n) (norm_nonneg _)) (mem_R.1 hf)
end GlobalTheory.BK
