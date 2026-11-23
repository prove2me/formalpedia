-- Prove2me | solution 1 for GlobalTheory.BK.S_le_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:43.634857+00:00
-- url     : https://prove2.me/submissions/39e6de08-ea3a-4163-a14d-47e28f35fd54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_rad_nonneg
import Theorems.Thm_GlobalTheory_BK_mem_R
import Theorems.Thm_GlobalTheory_BK_rad_le_one
import Theorems.Thm_GlobalTheory_BK_rad_pow

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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
include l
namespace GlobalTheory.BK
theorem _root_.solution (e : ℕ) [NeZero e] : S O K e ≤ R O K l (1 / e) := fun f hf => by
  refine mem_R.2 <| squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l _) n)) (fun n => ?_) hf.2
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans ?_ (norm_pow_le_norm_factorial l (n / e))
  rw [← rad_pow l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le n e)
end GlobalTheory.BK
