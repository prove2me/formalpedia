-- Prove2me | solution 1 for GlobalTheory.ContraRefl.res_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:36:45.912852+00:00
-- url     : https://prove2.me/submissions/8b81b9b1-5bc1-46b1-a950-535045e686d3

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
theorem _root_.solution (π : Representation ℂ G V) (K : Subgroup G) (l : fixed (contra π) K)
    (v : fixed π K) : res π K l v = ((l : smoothPart π.dual) : Module.Dual ℂ V) v := rfl
end GlobalTheory.ContraRefl
