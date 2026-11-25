-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.relSpan_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:06.477347+00:00
-- url     : https://prove2.me/submissions/aaee3a49-4e1f-43cc-bd3a-62e2295db082

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {χ : NN F n →* ℂ} {U V : Set (GL (Fin n) F)} (hUV : U ⊆ V) :
    relSpan χ U ≤ relSpan χ V := by
  refine Submodule.span_mono ?_
  rintro _ ⟨h, f, hf, rfl⟩
  exact ⟨h, f, supportedIn_mono hUV hf, rfl⟩
end GroundTheory.Automorphic.Whittaker
