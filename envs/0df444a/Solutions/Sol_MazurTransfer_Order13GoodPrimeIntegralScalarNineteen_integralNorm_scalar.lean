-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeIntegralScalarNineteen.integralNorm_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T05:15:59.522421+00:00
-- url     : https://prove2.me/submissions/f44a1c2d-609c-4288-bedb-3d7455295d8e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the unique integral extension of the actual
rational scalar morphism with scalar multiplication for the SAME
selected local relative group law.
Named downstream consumer: finite etale norm fibres and good-prime
unramified Kummer conditions for the order-13 norm maps.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormCompositionData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalGenericGroupIdentity_generic_group_law_units_equal
import Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormGroupLaws_generic_group_law_multiplications_equal
import Theorems.Thm_MazurTransfer_RelativeGroupLawInternalScalar_canonical_schemeNsmul
import Theorems.Thm_MazurTransfer_RelativeGroupLawBaseChangeNsmul_fibreRestrictAlong_schemeNsmul

noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian NeronSpecialFibreInfra
open Order13GoodPrimeLocalGenericGroupIdentity Order13GoodPrimeLocalGenericPicardComparison
open Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralNormComposition
open Order13LocalIntegralCoefficientMaps Order13ActualPicardDiamondSchemeEndomorphism
open Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
local instance integralNormScalarOriginalGroupProvider120261018 : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance integralNormScalarOriginalGroupProvider220261018 : GrpObj (Over.mk (localGenericPicard q hq).toBase) :=
  (genericRepresentationGroup q hq).grpObj

namespace MazurTransfer.GoodPrimeIntegralNormScalarProofHelpers20261018
theorem generic_group_law_units_equal_all {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)) :
    (genericLocalLaw q hq).one t = (genericRepresentedLaw q hq).one t := by
  have h := congrArg (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t))
    (generic_group_law_units_equal q hq)
  erw [RelativeGroupLaw.one_natural, RelativeGroupLaw.one_natural] at h
  exact h

theorem generic_group_law_nsmul_equal {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)) (n : ℕ)
    (x : SchemeHomOver t (localGenericPicard q hq).toBase) :
    (genericLocalLaw q hq).nsmul t n x = (genericRepresentedLaw q hq).nsmul t n x := by
  induction n with
  | zero =>
    erw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero]
    exact generic_group_law_units_equal_all q hq t
  | succ n ih =>
    erw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ,
      MazurTransfer.Order13GoodPrimeGenericNormGroupLaws.generic_group_law_multiplications_equal, ih]

theorem generic_group_law_schemeNsmul_equal (n : ℕ) :
    (genericLocalLaw q hq).schemeNsmul n = (genericRepresentedLaw q hq).schemeNsmul n := by
  have h := congrArg Subtype.val (generic_group_law_nsmul_equal q hq
    (localGenericPicard q hq).toBase n (schemeHomOverId _))
  erw [RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul,
    RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul, schemeHomOverId_coe, Category.id_comp] at h
  exact h

theorem localGenericNorm_scalar (n : ℕ) :
    localGenericNorm q hq ((𝟙 (Over.mk actualPicard.toBase)) ^ n) =
      ⟨(genericLocalLaw q hq).schemeNsmul n, (genericLocalLaw q hq).schemeNsmul_over n⟩ := by
  letI := actualLocalGenericOverIso_isMonHom q hq
  apply Subtype.ext
  change (localGenericNorm q hq ((𝟙 (Over.mk actualPicard.toBase)) ^ n)).val =
    (genericLocalLaw q hq).schemeNsmul n
  rw [generic_group_law_schemeNsmul_equal]
  change ((actualLocalGenericOverIso q hq).inv ≫
    ((𝟙 (Over.mk actualPicard.toBase)) ^ n) ≫ (actualLocalGenericOverIso q hq).hom).left =
      (relativeGroupLawOfGrpObj ℚ (localGenericPicard q hq).toBase).schemeNsmul n
  rw [MazurTransfer.RelativeGroupLawInternalScalar.canonical_schemeNsmul]
  have h : (actualLocalGenericOverIso q hq).inv ≫
      ((𝟙 (Over.mk actualPicard.toBase)) ^ n) ≫ (actualLocalGenericOverIso q hq).hom =
      (𝟙 (Over.mk (localGenericPicard q hq).toBase)) ^ n := by
    rw [← Category.assoc, MonObj.comp_pow, MonObj.pow_comp]
    simp only [Category.id_comp, Category.comp_id, Iso.inv_hom_id]
  exact congrArg Over.Hom.left h

end MazurTransfer.GoodPrimeIntegralNormScalarProofHelpers20261018
open MazurTransfer.GoodPrimeIntegralNormScalarProofHelpers20261018

theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (n : ℕ) :
    integralNorm q hq ((𝟙 (Over.mk actualPicard.toBase)) ^ n) =
      ⟨(localLaw q hq).schemeNsmul n, (localLaw q hq).schemeNsmul_over n⟩ := by
  symm
  apply integralNorm_unique
  change fibreRestrictAlong (specGenericFibreInclusion (LocalRing q) ℚ)
    (localPicard q hq).toBase (localPicard q hq).toBase _ = _
  rw [MazurTransfer.RelativeGroupLawBaseChangeNsmul.fibreRestrictAlong_schemeNsmul]
  exact (localGenericNorm_scalar q hq n).symm

#print axioms solution
