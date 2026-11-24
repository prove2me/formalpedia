-- Prove2me | solution 1 for GlobalTheory.SiteCoh.freeSheaf_map_tautSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:49:13.200885+00:00
-- url     : https://prove2.me/submissions/2266bb7f-79fc-4ffc-a451-60b142a74bc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Opposite Limits Abelian
universe w v u
noncomputable section
open GlobalTheory GlobalTheory.SiteCoh
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
namespace GlobalTheory.SiteCoh
theorem _root_.solution {U V : C} (i : V ⟶ U) :
    ((freeSheaf J).map i).hom.app (op V) (tautSection J V) =
      ((freeSheaf J).obj U).obj.map i.op (tautSection J U) := by
  have h₁ := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free.{v})) (op V))
    (FreeAbelianGroup.of (𝟙 V))
  have h₂ := ConcreteCategory.congr_hom
    ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free.{v})).naturality i.op)
    (FreeAbelianGroup.of (𝟙 U))
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  change (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free.{v})).app (op V)
      (FreeAbelianGroup.of (𝟙 V ≫ i)) =
    (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free.{v})).app (op V)
      (FreeAbelianGroup.of (i ≫ 𝟙 U))
  rw [Category.id_comp, Category.comp_id]
end GlobalTheory.SiteCoh
