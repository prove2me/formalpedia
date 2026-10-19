-- Prove2me | solution 1 for MazurTransfer.CurveIsoPicardPointMultiplicationTransport.transport_representation_relative_mul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T08:03:18.735549+00:00
-- url     : https://prove2.me/submissions/798d8e88-137a-4166-87fb-cc81593ddd93

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transporting a Picard representation along a pointed curve
isomorphism preserves the canonical relative point multiplication on its
unchanged representing scheme. Named downstream consumer: relative group
compatibility of the actual integral family's arithmetic field fibres.
-/
import Mathlib
import Definitions.Def_MazurTransfer_PointedCurvePicardRepresentationTransport
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTransfer.CurveHomRigidifiedLineBundlePullback MazurTransfer.CurveIsoRigidifiedLineBundleTransport
open MazurTransfer.CurveIsoPicardRepresentationTransport
open scoped CategoryTheory.MonObj
theorem solution {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (.of R))) c'}
    (e : C' ≅ C) (he : e.hom ≫ c = c') (hε : ε'.val ≫ e.hom = ε.val)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) (x y : SchemeHomOver t D.toBase) :
    ((show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D from h).relativeGroupLaw.mul t x y).val =
    ((show RepresentsRelSubPic c' ε' (algEquivZeroGroupCut c' ε').toSubPicCondition
        (relabelDesignation (c' := c') D) from transportRepresentation e he hε D h).relativeGroupLaw.mul t x y).val := by
  let hG : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D := h
  let h' := transportRepresentation e he hε D h
  let hG' : RepresentsRelSubPic c' ε' (algEquivZeroGroupCut c' ε').toSubPicCondition
      (relabelDesignation (c' := c') D) := h'
  letI := hG.grpObj
  have i1 : Nonempty ((h.poincare.pullbackAlong (hG.relativeGroupLaw.mul t x y)).L ≅
      ((h.poincare.pullbackAlong x).tensor (h.poincare.pullbackAlong y)).L) :=
    hG.nonempty_poincare_pullbackAlong_mul_iso
      (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  letI := hG'.grpObj
  have i2 : Nonempty ((h'.poincare.pullbackAlong (hG'.relativeGroupLaw.mul t x y)).L ≅
      ((h'.poincare.pullbackAlong x).tensor (h'.poincare.pullbackAlong y)).L) :=
    hG'.nonempty_poincare_pullbackAlong_mul_iso
      (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  have hi : (h'.poincare.pullbackAlong (hG.relativeGroupLaw.mul t x y)).L ≅
      (h'.poincare.pullbackAlong (hG'.relativeGroupLaw.mul t x y)).L :=
    (forward_pullbackAlong_iso e he hε (hG.relativeGroupLaw.mul t x y) h.poincare).symm ≪≫
      pullbackRigidified_congr e.hom he hε i1.some ≪≫
      Scheme.Modules.pullbackTensorObjIso (curvePullback e.hom he t) _ _ ≪≫
      (forward_pullbackAlong_iso e he hε x h.poincare ⊗ᵢ
        forward_pullbackAlong_iso e he hε y h.poincare) ≪≫ i2.some.symm
  exact congrArg Subtype.val (h'.ext_of_iso t _ _ ⟨hi⟩)
#print axioms solution
