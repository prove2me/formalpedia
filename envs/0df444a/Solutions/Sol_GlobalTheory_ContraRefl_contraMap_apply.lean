-- Prove2me | solution 1 for GlobalTheory.ContraRefl.contraMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:08.801783+00:00
-- url     : https://prove2.me/submissions/cadd3312-724f-4bdc-ae3c-b316e645506c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.ContraRefl
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.ContraRefl
theorem _root_.solution {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {σ : Representation ℂ G X} {τ : Representation ℂ G Y} (f : σ.IntertwiningMap τ)
    (l : smoothPart τ.dual) (x : X) :
    (contraMap f l : Module.Dual ℂ X) x = (l : Module.Dual ℂ Y) (f x) := rfl
end GlobalTheory.ContraRefl
