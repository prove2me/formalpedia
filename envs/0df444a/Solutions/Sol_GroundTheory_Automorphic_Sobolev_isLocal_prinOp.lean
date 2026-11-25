-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.isLocal_prinOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:54.872496+00:00
-- url     : https://prove2.me/submissions/17e6219f-1c85-42ee-bad4-ca3607d251f9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_isLocal_smulLeft
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_isLocal_iteratedLineDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → 𝓢(E, ℂ)) (w : ι → Fin m → E)
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution : IsLocal (prinOp a w) :=
  IsLocal.sum _ fun i _ ↦ (isLocal_smulLeft (a i).hasTemperateGrowth).comp
    (isLocal_iteratedLineDeriv (w i))
end GroundTheory.Automorphic.Sobolev
