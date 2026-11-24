-- Prove2me | solution 1 for GlobalTheory.exists_pullback_comp_iso_monHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:04.275487+00:00
-- url     : https://prove2.me/submissions/c37e16cc-247d-4a98-9d11-c2c95b6802ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {T S' S : Scheme.{0}} (f : S' ⟶ S) (g : S ⟶ T) (h : S' ⟶ T)
    (hh : h = f ≫ g) (G : Over T) [GrpObj G] :
    ∃ e : (Over.pullback h).obj G ≅ (Over.pullback f).obj ((Over.pullback g).obj G),
      IsMonHom e.hom ∧
        e.hom.left ≫ pullback.fst ((Over.pullback g).obj G).hom f ≫ pullback.fst G.hom g =
          pullback.fst G.hom h := by
  subst hh
  let m : (Over.pullback (f ≫ g)).mapMon.obj (Mon.mk G) ≅
      (Over.pullback f).mapMon.obj ((Over.pullback g).mapMon.obj (Mon.mk G)) :=
    (Functor.mapMonNatIso (Over.pullbackComp f g) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
  refine ⟨(Mon.forget _).mapIso m, ?_, ?_⟩
  · show IsMonHom m.hom.hom
    infer_instance
  · change (((Over.pullbackComp f g).hom.app G).left ≫ 𝟙 _) ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
    simp [Over.pullbackComp, Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]
end GlobalTheory
