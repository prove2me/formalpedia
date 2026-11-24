-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchwartzBaire.baireSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:09.322778+00:00
-- url     : https://prove2.me/submissions/7e439540-734e-47d4-a2f0-48d32e910b9e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Theorems.Thm_GlobalTheory_CompanionTheory_SchwartzBaire_completeSpace

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
theorem _root_.solution [CompleteSpace F] : BaireSpace 𝓢(E, F) := by
  have : CompleteSpace 𝓢(E, F) := completeSpace
  have : (𝓤 𝓢(E, F)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance
end GlobalTheory.CompanionTheory.SchwartzBaire
