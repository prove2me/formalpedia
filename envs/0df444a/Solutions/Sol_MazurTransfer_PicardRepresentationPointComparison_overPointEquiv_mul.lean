-- Prove2me | solution 1 for MazurTransfer.PicardRepresentationPointComparison.overPointEquiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T08:08:28.265979+00:00
-- url     : https://prove2.me/submissions/24d7d37c-d945-45ea-a13e-4c16cedc1fb1

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: classification by two representations of the same
relative Picard group subfunctor preserves canonical point multiplication.
Named downstream consumer: the actual integral family's arithmetic field
fibres, compared with the already published field representative.
Uses original official Anthropic FLT universal-bundle multiplication,
exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Mathlib
import Definitions.Def_MazurTransfer_PicardRepresentationPointComparison
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTransfer.PicardRepresentationPointComparison
open scoped CategoryTheory.MonObj

theorem solution {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {P : SubPicGroupCondition c ε} {D D' : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    (h' : RepresentsRelSubPic c ε P.toSubPicCondition D')
    {T : Over (Spec (.of R))} (a b : T ⟶ Over.mk D.toBase) :
    letI := h.grpObj
    letI := h'.grpObj
    overPointEquiv h h' T.hom (a * b) =
      overPointEquiv h h' T.hom a * overPointEquiv h h' T.hom b := by
  letI := h.grpObj
  letI := h'.grpObj
  let a' := overPointEquiv h h' T.hom a
  let b' := overPointEquiv h h' T.hom b
  have e0 := (pointMap_spec h h' T.hom (overHomToSchemeHomOver (a * b))).some
  have e1 := (h.nonempty_poincare_pullbackAlong_mul_iso a b).some
  have ea := (pointMap_spec h h' T.hom (overHomToSchemeHomOver a)).some
  have eb := (pointMap_spec h h' T.hom (overHomToSchemeHomOver b)).some
  have e2 := (h'.nonempty_poincare_pullbackAlong_mul_iso a' b').some
  have eq : pointMap h h' T.hom (overHomToSchemeHomOver (a * b)) =
      overHomToSchemeHomOver (a' * b') := by
    apply h'.ext_of_iso T.hom
    exact ⟨e0 ≪≫ e1 ≪≫ (ea.symm ⊗ᵢ eb.symm) ≪≫ e2.symm⟩
  apply Over.OverMorphism.ext
  exact congrArg Subtype.val eq

#print axioms solution
