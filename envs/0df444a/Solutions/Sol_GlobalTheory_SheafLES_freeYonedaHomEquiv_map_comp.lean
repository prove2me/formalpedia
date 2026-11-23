-- Prove2me | solution 1 for GlobalTheory.SheafLES.freeYonedaHomEquiv_map_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:24.290062+00:00
-- url     : https://prove2.me/submissions/371577cd-1d91-4073-8eac-34db727c3f99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
namespace GlobalTheory.SheafLES
theorem _root_.solution {U V : C} (i : V ⟶ U) {F : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeYoneda J).obj U ⟶ F) :
    freeYonedaHomEquiv V F ((freeYoneda J).map i ≫ φ) =
      F.obj.map i.op (freeYonedaHomEquiv U F φ) := by
  have h1 := (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv_naturality_left
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map i)) φ
  have h2 := (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left (yoneda.map i)
    ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F φ)
  have h3 := yonedaEquiv_naturality
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.obj
      ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F φ)) i
  refine Eq.trans ?_ h3.symm
  exact congrArg yonedaEquiv ((congrArg
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj V) F.obj) h1).trans h2)
end GlobalTheory.SheafLES
