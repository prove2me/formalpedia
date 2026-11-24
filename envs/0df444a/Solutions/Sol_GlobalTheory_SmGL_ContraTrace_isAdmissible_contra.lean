-- Prove2me | solution 1 for GlobalTheory.SmGL.ContraTrace.isAdmissible_contra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:23.43155+00:00
-- url     : https://prove2.me/submissions/c6055b7d-ae9a-48ba-bc13-25c5024a6416

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTrace
import Theorems.Thm_GlobalTheory_SmGL_ContraTrace_res_bijective
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_injective
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_contra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.ContraTrace
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.SmGL.ContraTrace
theorem _root_.solution [T2Space G] {π : Representation ℂ G V} (hπ : IsAdmissible π) :
    IsAdmissible (contra π) :=
  ⟨isSmooth_contra π, fun K ho hK =>
    haveI := hπ.2 K ho hK
    FiniteDimensional.of_injective (res π K) (res_bijective hπ.1 ho hK).1⟩
end GlobalTheory.SmGL.ContraTrace
