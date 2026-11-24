-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchwartzBaire.completeSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:14:11.084269+00:00
-- url     : https://prove2.me/submissions/7c09dd38-5266-422b-9b4b-47513aa57ef7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Theorems.Thm_GlobalTheory_CompanionTheory_SchwartzBaire_exists_tendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff Topology Uniformity
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchwartzBaire
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory.CompanionTheory.SchwartzBaire
theorem _root_.solution [CompleteSpace F] : CompleteSpace 𝓢(E, F) := by
  have : (𝓤 𝓢(E, F)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.complete_of_cauchySeq_tendsto fun f hf => exists_tendsto f hf
end GlobalTheory.CompanionTheory.SchwartzBaire
