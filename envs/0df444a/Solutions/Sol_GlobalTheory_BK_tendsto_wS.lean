-- Prove2me | solution 1 for GlobalTheory.BK.tendsto_wS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:55.176971+00:00
-- url     : https://prove2.me/submissions/4b2a1618-4e64-4806-b57d-6ca03eae4d31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_norm_factorial_le

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
theorem _root_.solution (e : ℕ) [NeZero e] : Tendsto (wS K e) atTop (𝓝 0) :=
  squeeze_zero (wS_nonneg e) (fun n => norm_factorial_le l (n / e))
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)).comp
      ((Nat.tendsto_div_const_atTop (Fact.out : l.Prime).ne_zero).comp
        (Nat.tendsto_div_const_atTop (NeZero.ne e))))
end GlobalTheory.BK
