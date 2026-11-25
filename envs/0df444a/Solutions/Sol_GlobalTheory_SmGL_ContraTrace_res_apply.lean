-- Prove2me | solution 1 for GlobalTheory.SmGL.ContraTrace.res_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:20:49.62922+00:00
-- url     : https://prove2.me/submissions/6a3eb1b7-c770-4f9e-a0ba-98eed8d643d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTrace

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
theorem _root_.solution (π : Representation ℂ G V) (K : Subgroup G) (l : fixed (contra π) K)
    (v : fixed π K) : res π K l v = (l.1 : Module.Dual ℂ V) v.1 := rfl
end GlobalTheory.SmGL.ContraTrace
