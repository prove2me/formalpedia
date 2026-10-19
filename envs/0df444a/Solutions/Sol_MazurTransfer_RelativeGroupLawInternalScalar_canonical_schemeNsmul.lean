-- Prove2me | solution 1 for MazurTransfer.RelativeGroupLawInternalScalar.canonical_schemeNsmul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T04:37:19.75717+00:00
-- url     : https://prove2.me/submissions/89bed383-f398-4dd1-a769-69edef3ead70

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the relative group law of an internal group object has
scalar morphisms equal to powers of its identity in the point group.
Named downstream consumer: the SAME order-13 integral norm composites
as multiplication by nineteen on the selected local Picard models.
-/
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul

noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj
universe u
namespace MazurTransfer.RelativeGroupLawInternalScalarProofHelpers20261018
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
  (f : A ⟶ Spec (CommRingCat.of R)) [GrpObj (Over.mk f)]

theorem canonical_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj R f).nsmul t n x =
      overHomToSchemeHomOver ((schemeHomOverToOverHom x) ^ n) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, pow_zero]; rfl
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ,
      relativeGroupLawOfGrpObj_mul, schemeHomOverToOverHom_overHomToSchemeHomOver]

end MazurTransfer.RelativeGroupLawInternalScalarProofHelpers20261018
open MazurTransfer.RelativeGroupLawInternalScalarProofHelpers20261018

theorem solution {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [GrpObj (Over.mk f)] (n : ℕ) :
    (relativeGroupLawOfGrpObj R f).schemeNsmul n =
      ((𝟙 (Over.mk f)) ^ n).left := by
  have h := congrArg Subtype.val (canonical_nsmul f f n (schemeHomOverId f))
  rw [RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul] at h
  have hid : schemeHomOverToOverHom (schemeHomOverId f) = 𝟙 (Over.mk f) := by
    apply Over.OverMorphism.ext
    rfl
  rw [hid] at h
  simpa only [schemeHomOverId_coe, Category.id_comp, overHomToSchemeHomOver_coe] using h

#print axioms solution
