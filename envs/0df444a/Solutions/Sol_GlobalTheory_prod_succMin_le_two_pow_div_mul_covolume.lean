-- Prove2me | solution 1 for GlobalTheory.prod_succMin_le_two_pow_div_mul_covolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:30.050159+00:00
-- url     : https://prove2.me/submissions/0ae286bf-9f86-4369-becb-92d878471da5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Theorems.Thm_GlobalTheory_volume_real_unitBall_pos
import Theorems.Thm_GlobalTheory_prod_succMin_mul_volume_unitBall_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MeasureTheory
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
namespace GlobalTheory
theorem _root_.solution :
    ∏ i : Fin (finrank ℝ E), succMin L (i + 1) ≤
      2 ^ finrank ℝ E / volume.real (Metric.ball (0 : E) 1) * ZLattice.covolume L := by
  rw [div_mul_eq_mul_div, le_div_iff₀ volume_real_unitBall_pos]
  exact prod_succMin_mul_volume_unitBall_le L
end GlobalTheory
