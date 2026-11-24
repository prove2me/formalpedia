-- Prove2me | solution 1 for GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:16:07.715799+00:00
-- url     : https://prove2.me/submissions/fa118ff9-3388-41ef-9afb-f0f0e69415df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSumStatement
import Theorems.Thm_GlobalTheory_Phase_GaussSum_ph_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [AddCommGroup M] [Fintype M] (f : M → ℂ), Quad ⊤ f → Ph (∑ x, f x) := by
  first | exact @GlobalTheory.Phase.GaussSum.ph_sum | exact GlobalTheory.Phase.GaussSum.ph_sum | (intros; apply GlobalTheory.Phase.GaussSum.ph_sum <;> assumption)
end _root_.GlobalTheory.T
