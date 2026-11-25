-- Prove2me | solution 1 for GlobalTheory.prod_succMin_le_rpow_mul_covolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:01.485858+00:00
-- url     : https://prove2.me/submissions/ed138921-8693-4772-af6a-2636068d3fef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Theorems.Thm_GlobalTheory_two_pow_div_volume_unitBall_le
import Theorems.Thm_GlobalTheory_prod_succMin_le_two_pow_div_mul_covolume

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
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) * ZLattice.covolume L :=
  (prod_succMin_le_two_pow_div_mul_covolume L).trans
    (mul_le_mul_of_nonneg_right (two_pow_div_volume_unitBall_le E)
      (ZLattice.covolume_pos L volume).le)
end GlobalTheory
