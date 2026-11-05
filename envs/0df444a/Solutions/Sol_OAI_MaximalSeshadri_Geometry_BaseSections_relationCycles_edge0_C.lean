-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.BaseSections.relationCycles_edge0_C
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:22:26.376216+00:00
-- url     : https://prove2.me/submissions/1330f2db-fc93-46ff-b291-f2e004ced48d

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

set_option Elab.async false
set_option linter.all false

section
namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

section
variable {space : TopCat.{0}}
  (ringSheaf : Sheaf (Opens.grothendieckTopology space) RingCat.{0})
  (first second third : Opens space) {target : SheafOfModules ringSheaf}
  (morphism : tripleVertices ringSheaf first second third ⟶ target)

private lemma tripleBoundary_third :
    (biprod.inr ≫ biprod.inr ≫ tripleToRelations ringSheaf first second third) ≫
        (kernel.ι (tripleG ringSheaf first second third) ≫ morphism) =
      freeOpenMap ringSheaf (homOfLE inf_le_left) ≫
          (biprod.inl ≫ biprod.inr ≫ morphism) -
        freeOpenMap ringSheaf (homOfLE inf_le_right) ≫
          (biprod.inr ≫ biprod.inr ≫ morphism) := by
  simp only [tripleToRelations, Category.assoc, kernel.lift_ι_assoc, tripleD,
    biprod.inr_desc_assoc, Preadditive.sub_comp]
end

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.planeBoundariesLinear

attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.planeBoundariesFreeHomGroup

attribute [local instance] baseHomModule
variable (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X)

lemma relation_boundary_C (g : planeVertices s ⟶ L.sheaf) :
    ((relationCycles k s L (planeRelIota s ≫ g)).val.2.2 : _) =
      homChart k L.sheaf (planeTriple_le s 1) (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ g) -
      homChart k L.sheaf (planeTriple_le s 2) (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ g) := by
  change homChart k L.sheaf _ ((biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ (planeRelIota s ≫ g)) = _
  have composite := tripleBoundary_third X.ringCatSheaf
    (SectionOpens.isoOpen (s 0)) (SectionOpens.isoOpen (s 1))
    (SectionOpens.isoOpen (s 2)) g
  exact (congrArg (homChart k L.sheaf _) composite).trans
    ((map_sub (homChart k L.sheaf _) _ _).trans
      (congrArg₂ (· - ·) (homChart_natural k L.sheaf _ _ _)
        (homChart_natural k L.sheaf _ _ _)))

private lemma homChart_desc_second (target : X.Modules) {first second third chart : X.Opens}
    (containment : chart ≤ second)
    (firstMap : BaseHom k (freeOpen X.ringCatSheaf first) target)
    (secondMap : BaseHom k (freeOpen X.ringCatSheaf second) target)
    (thirdMap : BaseHom k (freeOpen X.ringCatSheaf third) target) :
    homChart k target containment
      (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫
        biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫
        biprod.desc (C := SheafOfModules X.ringCatSheaf) firstMap
          (biprod.desc (C := SheafOfModules X.ringCatSheaf) secondMap thirdMap)) =
      homChart k target containment secondMap :=
  congrArg (homChart k target containment)
    ((congrArg (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ ·) (biprod.inr_desc (C := SheafOfModules X.ringCatSheaf) _ _)).trans (biprod.inl_desc (C := SheafOfModules X.ringCatSheaf) _ _))

private lemma homChart_desc_third (target : X.Modules) {first second third chart : X.Opens}
    (containment : chart ≤ third)
    (firstMap : BaseHom k (freeOpen X.ringCatSheaf first) target)
    (secondMap : BaseHom k (freeOpen X.ringCatSheaf second) target)
    (thirdMap : BaseHom k (freeOpen X.ringCatSheaf third) target) :
    homChart k target containment
      (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫
        biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫
        biprod.desc (C := SheafOfModules X.ringCatSheaf) firstMap
          (biprod.desc (C := SheafOfModules X.ringCatSheaf) secondMap thirdMap)) =
      homChart k target containment thirdMap :=
  congrArg (homChart k target containment)
    ((congrArg (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ ·) (biprod.inr_desc (C := SheafOfModules X.ringCatSheaf) _ _)).trans (biprod.inr_desc (C := SheafOfModules X.ringCatSheaf) _ _))

lemma relationCycles_edge0_C (x : ↥(planePair k s L 0 1 ⊓ planePair k s L 0 2))
    (f : BaseHom k (freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s 0))) L.sheaf)
    (_hf : homChart k L.sheaf (planeTriple_le s 0) f = x.val) :
    (relationCycles k s L (planeRelIota s ≫ biprod.desc (C := SheafOfModules X.ringCatSheaf) f (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 0))).val.2.2.val = 0 := by
  refine (relation_boundary_C k s L _).trans ?_
  refine (congrArg₂ (· - ·)
    (homChart_desc_second k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 1) f 0 0)
    (homChart_desc_third k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 2) f 0 0)).trans ?_
  simp only [map_zero, sub_zero]

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.BaseSections.relationCycles_edge0_C := @OAI.MaximalSeshadri.Geometry.BaseSections.relationCycles_edge0_C
