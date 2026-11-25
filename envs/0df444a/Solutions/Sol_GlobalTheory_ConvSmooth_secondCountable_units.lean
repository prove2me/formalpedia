-- Prove2me | solution 1 for GlobalTheory.ConvSmooth.secondCountable_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:38:09.875066+00:00
-- url     : https://prove2.me/submissions/18ed3b5e-0ef0-48b4-807f-2aa05c7abdbe

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralInvLeOfSupportCompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRightStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvSmoothCompactSupport
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_secondCountableTopology


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.ConvSmooth
namespace GlobalTheory.ConvSmooth
theorem _root_.solution (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] : SecondCountableTopology 𝔸ˣ := by
  haveI : ProperSpace 𝔸 := FiniteDimensional.proper ℝ 𝔸
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
end GlobalTheory.ConvSmooth
