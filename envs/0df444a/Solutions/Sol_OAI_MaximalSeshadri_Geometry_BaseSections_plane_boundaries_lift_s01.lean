-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:01.608903+00:00
-- url     : https://prove2.me/submissions/ba04fd39-7a9f-4266-941a-e80f663fd476

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_BaseSections_relationCycles_edge1_s01

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PlaneBoundaries
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

private lemma tripleBoundary_first :
    (biprod.inl ≫ tripleToRelations ringSheaf first second third) ≫
        (kernel.ι (tripleG ringSheaf first second third) ≫ morphism) =
      freeOpenMap ringSheaf (homOfLE inf_le_left) ≫ (biprod.inl ≫ morphism) -
        freeOpenMap ringSheaf (homOfLE inf_le_right) ≫
          (biprod.inl ≫ biprod.inr ≫ morphism) := by
  simp only [tripleToRelations, Category.assoc, kernel.lift_ι_assoc, tripleD,
    biprod.inl_desc_assoc, Preadditive.sub_comp]

private lemma tripleBoundary_second :
    (biprod.inl ≫ biprod.inr ≫ tripleToRelations ringSheaf first second third) ≫
        (kernel.ι (tripleG ringSheaf first second third) ≫ morphism) =
      -(freeOpenMap ringSheaf (homOfLE inf_le_left) ≫ (biprod.inl ≫ morphism)) +
        freeOpenMap ringSheaf (homOfLE inf_le_right) ≫
          (biprod.inr ≫ biprod.inr ≫ morphism) := by
  simp only [tripleToRelations, Category.assoc, kernel.lift_ι_assoc, tripleD,
    biprod.inl_desc_assoc, biprod.inr_desc_assoc, Preadditive.add_comp,
    Preadditive.neg_comp]

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
attribute [local instance] baseHomModule
variable (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X)

attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.planeBoundariesFreeHomGroup
lemma relation_boundary_A (g : planeVertices s ⟶ L.sheaf) :
    ((relationCycles k s L (planeRelIota s ≫ g)).val.1 : _) =
      homChart k L.sheaf (planeTriple_le s 0) (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ g) -
      homChart k L.sheaf (planeTriple_le s 1) (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ g) := by
  change homChart k L.sheaf _ ((biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ (planeRelIota s ≫ g)) = _
  have composite := tripleBoundary_first X.ringCatSheaf
    (SectionOpens.isoOpen (s 0)) (SectionOpens.isoOpen (s 1))
    (SectionOpens.isoOpen (s 2)) g
  exact (congrArg (homChart k L.sheaf _) composite).trans
    ((map_sub (homChart k L.sheaf _) _ _).trans
      (congrArg₂ (· - ·) (homChart_natural k L.sheaf _ _ _)
        (homChart_natural k L.sheaf _ _ _)))

lemma relation_boundary_B (g : planeVertices s ⟶ L.sheaf) :
    ((relationCycles k s L (planeRelIota s ≫ g)).val.2.1 : _) =
      -homChart k L.sheaf (planeTriple_le s 0) (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ g) +
      homChart k L.sheaf (planeTriple_le s 2) (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ g) := by
  change homChart k L.sheaf _ ((biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ (planeRelIota s ≫ g)) = _
  have composite := tripleBoundary_second X.ringCatSheaf
    (SectionOpens.isoOpen (s 0)) (SectionOpens.isoOpen (s 1))
    (SectionOpens.isoOpen (s 2)) g
  refine (congrArg (homChart k L.sheaf _) composite).trans ?_
  refine (map_add (homChart k L.sheaf _) _ _).trans ?_
  refine (congrArg₂ (· + ·) (map_neg (homChart k L.sheaf _) _) rfl).trans ?_
  exact congrArg₂ (· + ·) (congrArg Neg.neg (homChart_natural k L.sheaf _ _ _))
    (homChart_natural k L.sheaf _ _ _)

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

lemma planeCycles_ext {x y : cycles (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)}
    (ha : x.val.1.val = y.val.1.val) (hb : x.val.2.1.val = y.val.2.1.val)
    (hc : x.val.2.2.val = y.val.2.2.val) : x = y :=
  Subtype.ext (Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) (Subtype.ext hc)))

private lemma homChart_desc_first (target : X.Modules) {first second third chart : X.Opens}
    (containment : chart ≤ first)
    (firstMap : BaseHom k (freeOpen X.ringCatSheaf first) target)
    (secondMap : BaseHom k (freeOpen X.ringCatSheaf second) target)
    (thirdMap : BaseHom k (freeOpen X.ringCatSheaf third) target) :
    homChart k target containment
      (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫
        biprod.desc (C := SheafOfModules X.ringCatSheaf) firstMap
          (biprod.desc (C := SheafOfModules X.ringCatSheaf) secondMap thirdMap)) =
      homChart k target containment firstMap :=
  congrArg (homChart k target containment) (biprod.inl_desc (C := SheafOfModules X.ringCatSheaf) _ _)

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

lemma relationCycles_edge0_A (x : ↥(planePair k s L 0 1 ⊓ planePair k s L 0 2))
    (f : BaseHom k (freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s 0))) L.sheaf)
    (hf : homChart k L.sheaf (planeTriple_le s 0) f = x.val) :
    (relationCycles k s L (planeRelIota s ≫ biprod.desc (C := SheafOfModules X.ringCatSheaf) f (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 0))).val.1.val = x.val := by
  refine (relation_boundary_A k s L _).trans ?_
  refine (congrArg₂ (· - ·)
    (homChart_desc_first k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 0) f 0 0)
    (homChart_desc_second k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 1) f 0 0)).trans ?_
  simp only [map_zero, sub_zero]
  exact hf

lemma relationCycles_edge0_B (x : ↥(planePair k s L 0 1 ⊓ planePair k s L 0 2))
    (f : BaseHom k (freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s 0))) L.sheaf)
    (hf : homChart k L.sheaf (planeTriple_le s 0) f = x.val) :
    (relationCycles k s L (planeRelIota s ≫ biprod.desc (C := SheafOfModules X.ringCatSheaf) f (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 0))).val.2.1.val = -x.val := by
  refine (relation_boundary_B k s L _).trans ?_
  refine (congrArg₂ (· + ·) (congrArg Neg.neg
    (homChart_desc_first k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 0) f 0 0))
    (homChart_desc_third k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 2) f 0 0)).trans ?_
  simp only [map_zero, add_zero]
  exact congrArg Neg.neg hf

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

lemma relationCycles_edge0 (x : ↥(planePair k s L 0 1 ⊓ planePair k s L 0 2))
    (f : BaseHom k (freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s 0))) L.sheaf)
    (hf : homChart k L.sheaf (planeTriple_le s 0) f = x.val) :
    relationCycles k s L (planeRelIota s ≫ biprod.desc (C := SheafOfModules X.ringCatSheaf) f (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 0)) = edgeAB _ _ _ x :=
  planeCycles_ext k s L (relationCycles_edge0_A k s L x f hf)
    (relationCycles_edge0_B k s L x f hf) (relationCycles_edge0_C k s L x f hf)

lemma relationCycles_edge2_A (x : ↥(planePair k s L 0 2 ⊓ planePair k s L 1 2))
    (f : BaseHom k (freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s 2))) L.sheaf)
    (_hf : homChart k L.sheaf (planeTriple_le s 2) f = x.val) :
    (relationCycles k s L (planeRelIota s ≫ biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 f))).val.1.val = 0 := by
  refine (relation_boundary_A k s L _).trans ?_
  refine (congrArg₂ (· - ·)
    (homChart_desc_first k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 0) 0 0 f)
    (homChart_desc_second k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 1) 0 0 f)).trans ?_
  simp only [map_zero, sub_zero]

lemma relationCycles_edge2_B (x : ↥(planePair k s L 0 2 ⊓ planePair k s L 1 2))
    (f : BaseHom k (freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s 2))) L.sheaf)
    (hf : homChart k L.sheaf (planeTriple_le s 2) f = x.val) :
    (relationCycles k s L (planeRelIota s ≫ biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 f))).val.2.1.val = x.val := by
  refine (relation_boundary_B k s L _).trans ?_
  refine (congrArg₂ (· + ·) (congrArg Neg.neg
    (homChart_desc_first k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 0) 0 0 f))
    (homChart_desc_third k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 2) 0 0 f)).trans ?_
  simp only [map_zero, neg_zero, zero_add]
  exact hf

lemma relationCycles_edge2_C (x : ↥(planePair k s L 0 2 ⊓ planePair k s L 1 2))
    (f : BaseHom k (freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s 2))) L.sheaf)
    (hf : homChart k L.sheaf (planeTriple_le s 2) f = x.val) :
    (relationCycles k s L (planeRelIota s ≫ biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 f))).val.2.2.val = -x.val := by
  refine (relation_boundary_C k s L _).trans ?_
  refine (congrArg₂ (· - ·)
    (homChart_desc_second k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 1) 0 0 f)
    (homChart_desc_third k L.sheaf (first := SectionOpens.isoOpen (s 0)) (second := SectionOpens.isoOpen (s 1)) (third := SectionOpens.isoOpen (s 2))
      (planeTriple_le s 2) 0 0 f)).trans ?_
  simp only [map_zero, zero_sub]
  exact congrArg Neg.neg hf

lemma relationCycles_edge2 (x : ↥(planePair k s L 0 2 ⊓ planePair k s L 1 2))
    (f : BaseHom k (freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s 2))) L.sheaf)
    (hf : homChart k L.sheaf (planeTriple_le s 2) f = x.val) :
    relationCycles k s L (planeRelIota s ≫ biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 f)) = edgeBC _ _ _ x :=
  planeCycles_ext k s L (relationCycles_edge2_A k s L x f hf)
    (relationCycles_edge2_B k s L x f hf) (relationCycles_edge2_C k s L x f hf)

lemma plane_boundaries_lift_s01_oai :
    vertexBoundaries (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)
      (planeVertex k s L) ≤ (relationBoundaries k s L).map (relationCycles k s L) := by
  unfold vertexBoundaries boundaries
  apply sup_le
  · apply sup_le
    · rintro _ ⟨x,hx,rfl⟩
      change x.val ∈ planeVertex k s L 0 at hx
      rw [planeVertex,← homChart_range] at hx
      obtain ⟨f,hf⟩ := hx
      exact ⟨_,⟨biprod.desc (C := SheafOfModules X.ringCatSheaf) f (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 0),rfl⟩,relationCycles_edge0 k s L x f hf⟩
    · rintro _ ⟨x,hx,rfl⟩
      change x.val ∈ planeVertex k s L 1 at hx
      rw [planeVertex,← homChart_range] at hx
      obtain ⟨f,hf⟩ := hx
      exact ⟨_,⟨biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 (biprod.desc (C := SheafOfModules X.ringCatSheaf) (-f) 0),rfl⟩,relationCycles_edge1_s01 k s L x f hf⟩
  · rintro _ ⟨x,hx,rfl⟩
    change x.val ∈ planeVertex k s L 2 at hx
    rw [planeVertex,← homChart_range] at hx
    obtain ⟨f,hf⟩ := hx
    exact ⟨_,⟨biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 (biprod.desc (C := SheafOfModules X.ringCatSheaf) 0 f),rfl⟩,relationCycles_edge2 k s L x f hf⟩

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift_s01_oai := @OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift_s01_oai
