-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_scalar_nineteen_and_finite_etale_norm_fibres
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T10:14:15.596811+00:00
-- url     : https://prove2.me/submissions/e81f646f-57b8-4e0c-9c0e-ab523892d381

import Theorems.Thm_MazurTransfer_RelativeGroupLawInternalScalar_canonical_schemeNsmul
import Theorems.Thm_MazurTransfer_RelativeGroupLawBaseChangeNsmul_fibreRestrictAlong_schemeNsmul
import Theorems.Thm_MazurTransfer_relative_group_norm_factors_finite_of_invertible_scalar
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both actual original norm composites are scalar nineteen for the same chosen dyadic law, and both norm fibres are finite etale over every test scheme.
Named downstream consumer: actual dyadic norm inertia and unramified Kummer conditions at two.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalScalarNormScopedGroupProvidersV220261019
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison Order13DyadicMixedPicardGeometry
open Order13DyadicMixedGenericNorms Order13DyadicMixedIntegralNormExtensions
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedGenericNormGroupLaws
open Order13DyadicMixedIntegralNormGroupLaws Order13DyadicMixedIntegralNormComposition
open scoped CategoryTheory.MonObj
open Order13DyadicMixedIntegralScalarNineteen Order13DyadicMixedScalarInputs
open Order13DyadicMixedIntegralNormFinite Order13DyadicMixedIntegralNormEtale
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.originalDyadicChosenPicardNeronPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instFactPrimeOfNatNat_order13DyadicMixedIntegralScalarNineteen
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralScalarNineteen
attribute [local instance] MazurTransfer.Order13DyadicMixedScalarInputs.instFactPrimeOfNatNat_order13DyadicMixedScalarInputs
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormFinite.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormFinite
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard_order13DyadicMixedIntegralScalarNineteen
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormEtale.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormEtale

namespace MazurTransfer.ActualDyadicOriginalScalarNineteenFiniteEtaleProofBoundaryTheoremBundleV320261019
end MazurTransfer.ActualDyadicOriginalScalarNineteenFiniteEtaleProofBoundaryTheoremBundleV320261019


/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: The same original integral norm composites equal scalar nineteen for the original chosen dyadic Picard law, and both original norm fibres are finite etale over every test scheme.
Named downstream consumer: Actual dyadic norm inertia and unramified Kummer conditions at two.
Original per-file headers and attribution are retained below.
-/

noncomputable section
namespace MazurTransfer.OriginalDyadicScalarUnitProof20261019
open AlgebraicGeometry MazurTransfer.Order13DyadicMixedQuadraticCharts
open MazurTransfer.Order13LocalIntegralCoefficientMaps
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
theorem dyadic_integer_unit (n : ℕ) (hn : ¬ (2 : ℤ) ∣ (n : ℤ)) :
    IsUnit (n : BaseRing) := by
  have h : (n : ℤ) ∈ (primeIdeal 2).primeCompl := by
    change (n : ℤ) ∉ Ideal.span {(2 : ℤ)}
    rw [Ideal.mem_span_singleton]
    exact hn
  simpa only [_root_.map_natCast] using IsLocalization.map_units BaseRing ⟨(n : ℤ), h⟩

end MazurTransfer.OriginalDyadicScalarUnitProof20261019
end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the following checked good-prime proof is adapted to the
SAME selected actual dyadic Picard, its represented group law and actual
rational norm maps. No unit assumption on two or 104 is added.
Named downstream consumer: finite etale dyadic norm fibres and their
arithmetic inertia/Kummer condition. Original method and attribution follow.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the unique integral extension of the actual
rational scalar morphism with scalar multiplication for the SAME
selected local relative group law.
Named downstream consumer: finite etale norm fibres and good-prime
unramified Kummer conditions for the order-13 norm maps.
-/

noncomputable section
namespace MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralScalarNineteen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian NeronSpecialFibreInfra
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedRationalPicardComparison
open Order13DyadicMixedGenericNormGroupLaws Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedIntegralNormExtensions Order13DyadicMixedIntegralNormComposition
open Order13DyadicMixedQuadraticCharts Order13ActualPicardDiamondSchemeEndomorphism
open Order13DyadicMixedRationalPicardComparison Order13DyadicMixedRationalPicardComparison
open RelativeGroupLawInternalScalar RelativeGroupLawBaseChangeNsmul
open scoped CategoryTheory.MonObj
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instFactPrimeOfNatNat_order13DyadicMixedIntegralScalarNineteen
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralScalarNineteen
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralScalarNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard_order13DyadicMixedIntegralScalarNineteen

theorem generic_group_law_units_equal_all {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)) :
    (genericLocalLaw).one t = (genericRepresentedLaw).one t := by
  have h := congrArg (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t))
    (generic_group_law_units_equal)
  erw [RelativeGroupLaw.one_natural, RelativeGroupLaw.one_natural] at h
  exact h

theorem generic_group_law_nsmul_equal {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)) (n : ℕ)
    (x : SchemeHomOver t (rationalPicard).toBase) :
    (genericLocalLaw).nsmul t n x = (genericRepresentedLaw).nsmul t n x := by
  induction n with
  | zero =>
    erw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero]
    exact generic_group_law_units_equal_all t
  | succ n ih =>
    erw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ,
      generic_group_law_multiplications_equal, ih]

theorem generic_group_law_schemeNsmul_equal (n : ℕ) :
    (genericLocalLaw).schemeNsmul n = (genericRepresentedLaw).schemeNsmul n := by
  have h := congrArg Subtype.val (generic_group_law_nsmul_equal
    (rationalPicard).toBase n (schemeHomOverId _))
  erw [RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul,
    RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul, schemeHomOverId_coe, Category.id_comp] at h
  exact h

theorem localGenericNorm_scalar (n : ℕ) :
    genericNorm ((𝟙 (Over.mk actualPicard.toBase)) ^ n) =
      ⟨(genericLocalLaw).schemeNsmul n, (genericLocalLaw).schemeNsmul_over n⟩ := by
  letI := actualDyadicRationalOverIso_isMonHom
  apply Subtype.ext
  change (genericNorm ((𝟙 (Over.mk actualPicard.toBase)) ^ n)).val =
    (genericLocalLaw).schemeNsmul n
  rw [generic_group_law_schemeNsmul_equal]
  change ((actualDyadicRationalOverIso).inv ≫
    ((𝟙 (Over.mk actualPicard.toBase)) ^ n) ≫ (actualDyadicRationalOverIso).hom).left =
      (relativeGroupLawOfGrpObj ℚ (rationalPicard).toBase).schemeNsmul n
  rw [canonical_schemeNsmul]
  have h : (actualDyadicRationalOverIso).inv ≫
      ((𝟙 (Over.mk actualPicard.toBase)) ^ n) ≫ (actualDyadicRationalOverIso).hom =
      (𝟙 (Over.mk (rationalPicard).toBase)) ^ n := by
    rw [← Category.assoc, MonObj.comp_pow, MonObj.pow_comp]
    simp only [Category.id_comp, Category.comp_id, Iso.inv_hom_id]
  exact congrArg Over.Hom.left h

theorem integralNorm_scalar (n : ℕ) :
    integralNorm ((𝟙 (Over.mk actualPicard.toBase)) ^ n) =
      ⟨(dyadicLaw).schemeNsmul n, (dyadicLaw).schemeNsmul_over n⟩ := by
  symm
  apply integralNorm_unique
  change fibreRestrictAlong (specGenericFibreInclusion (BaseRing) ℚ)
    (dyadicPicard).toBase (dyadicPicard).toBase _ = _
  rw [fibreRestrictAlong_schemeNsmul]
  exact (localGenericNorm_scalar n).symm

theorem integralScalarNineteen_eq_local_schemeNsmul :
    (integralScalarNineteen).val = (dyadicLaw).schemeNsmul 19 :=
  congrArg Subtype.val (integralNorm_scalar 19)

theorem integralPi_comp_integralPiConjugate_eq_local_schemeNsmul :
    (integralPi).val ≫ (integralPiConjugate).val =
      (dyadicLaw).schemeNsmul 19 := by
  have h := congrArg Subtype.val (integralPi_comp_integralPiConjugate)
  exact h.trans (integralScalarNineteen_eq_local_schemeNsmul)

theorem integralPiConjugate_comp_integralPi_eq_local_schemeNsmul :
    (integralPiConjugate).val ≫ (integralPi).val =
      (dyadicLaw).schemeNsmul 19 := by
  have h := congrArg Subtype.val (integralPiConjugate_comp_integralPi)
  exact h.trans (integralScalarNineteen_eq_local_schemeNsmul)

end MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralScalarNineteen
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralScalarNineteen.integralNorm_scalar
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralScalarNineteen.integralPi_comp_integralPiConjugate_eq_local_schemeNsmul
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralScalarNineteen.integralPiConjugate_comp_integralPi_eq_local_schemeNsmul

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: nineteen is a unit in Z_(2), and the SAME dyadic Picard
relative law is commutative. Named downstream consumer: finite flat scalar
nineteen and the two actual dyadic norm factors.
-/

noncomputable section
namespace MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedScalarInputs
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13ActualDyadicMixedPicardNeronModel Order13DyadicMixedQuadraticPicardGeometryInputs
attribute [local instance] MazurTransfer.Order13DyadicMixedScalarInputs.instFactPrimeOfNatNat_order13DyadicMixedScalarInputs

theorem local_unit_nineteen : IsUnit (19 : BaseRing) :=
  MazurTransfer.OriginalDyadicScalarUnitProof20261019.dyadic_integer_unit 19 (by norm_num)

theorem local_law_isCommutative : dyadicLaw.IsCommutative :=
  (show RepresentsRelSubPic (curveToBase BaseRing) zeroSection
    (algEquivZeroGroupCut (curveToBase BaseRing) zeroSection).toSubPicCondition
      dyadicPicard from dyadicRepresentation).relativeGroupLaw_isCommutative

end MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedScalarInputs
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedScalarInputs.local_unit_nineteen
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedScalarInputs.local_law_isCommutative

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the following checked good-prime proof is adapted to the
SAME selected actual dyadic Picard, its represented group law and actual
rational norm maps. No unit assumption on two or 104 is added.
Named downstream consumer: finite etale dyadic norm fibres and their
arithmetic inertia/Kummer condition. Original method and attribution follow.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finiteness and formal unramifiedness of the SAME selected
integral norm extensions at every prime away from 104 and nineteen.
Named downstream consumer: finite etale norm fibres and good-prime
unramified Kummer conditions for the order-13 norm maps.
-/

noncomputable section
namespace MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormFinite
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13ActualDyadicMixedPicardNeronModel ScalarNormTheoremBodyV220261019.Order13DyadicMixedScalarInputs
open Order13DyadicMixedIntegralNormExtensions ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralScalarNineteen
open Order13DyadicMixedQuadraticCharts
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormFinite.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormFinite


theorem integral_norms_finite :
    IsFinite (integralPi).val ∧ IsFinite (integralPiConjugate).val := by
  letI : IsProper (dyadicPicard).toBase := (dyadicPicard_geometry).2.1
  exact MazurTransfer.relative_group_norm_factors_finite_of_invertible_scalar
    (dyadicPicard).toBase (dyadicLaw) (local_law_isCommutative)
    19 (local_unit_nineteen) (integralPi).val (integralPiConjugate).val
    (integralPi).property (integralPiConjugate).property
    (integralPi_comp_integralPiConjugate_eq_local_schemeNsmul)
    (integralPiConjugate_comp_integralPi_eq_local_schemeNsmul)

theorem integral_norms_formallyUnramified :
    FormallyUnramified (integralPi).val ∧
      FormallyUnramified (integralPiConjugate).val := by
  have hs := RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
    (dyadicLaw) (local_law_isCommutative) 19 (local_unit_nineteen)
  letI : FormallyUnramified ((integralPi).val ≫ (integralPiConjugate).val) := by
    rw [integralPi_comp_integralPiConjugate_eq_local_schemeNsmul]
    exact hs
  letI : FormallyUnramified ((integralPiConjugate).val ≫ (integralPi).val) := by
    rw [integralPiConjugate_comp_integralPi_eq_local_schemeNsmul]
    exact hs
  exact ⟨FormallyUnramified.of_comp (integralPi).val (integralPiConjugate).val,
    FormallyUnramified.of_comp (integralPiConjugate).val (integralPi).val⟩

end MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormFinite
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormFinite.integral_norms_finite
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormFinite.integral_norms_formallyUnramified

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the following checked good-prime proof is adapted to the
SAME selected actual dyadic Picard, its represented group law and actual
rational norm maps. No unit assumption on two or 104 is added.
Named downstream consumer: finite etale dyadic norm fibres and their
arithmetic inertia/Kummer condition. Original method and attribution follow.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite etale fibres of the SAME selected integral norm
extensions at every prime away from 104 and nineteen. The group law and
multiplication by nineteen are those of the selected local Picard model.
Named downstream consumer: good-prime unramified Kummer conditions.
-/

noncomputable section
namespace MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormEtale
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13ActualDyadicMixedPicardNeronModel ScalarNormTheoremBodyV220261019.Order13DyadicMixedScalarInputs
open Order13DyadicMixedIntegralNormExtensions ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralScalarNineteen
open ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormFinite Order13DyadicMixedQuadraticCharts
open Order13DyadicMixedGenericNorms Order13DyadicMixedPicardGeometry
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormEtale.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormEtale

theorem local_scalar_nineteen_finite_and_flat :
    IsFinite ((dyadicLaw).schemeNsmul 19) ∧ Flat ((dyadicLaw).schemeNsmul 19) :=
  RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit
    (dyadicLaw) (dyadicPicard_abelian) (local_law_isCommutative)
    19 (local_unit_nineteen)

theorem local_scalar_nineteen_etale : Etale ((dyadicLaw).schemeNsmul 19) := by
  letI : Smooth (dyadicPicard).toBase := (dyadicPicard_geometry).1
  letI : IsLocallyNoetherian (dyadicPicard).P :=
    LocallyOfFiniteType.isLocallyNoetherian (dyadicPicard).toBase
  letI : IsFinite ((dyadicLaw).schemeNsmul 19) :=
    (local_scalar_nineteen_finite_and_flat).1
  letI : Flat ((dyadicLaw).schemeNsmul 19) :=
    (local_scalar_nineteen_finite_and_flat).2
  letI : FormallyUnramified ((dyadicLaw).schemeNsmul 19) :=
    RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
      (dyadicLaw) (local_law_isCommutative) 19 (local_unit_nineteen)
  exact Etale.of_formallyUnramified_of_flat ((dyadicLaw).schemeNsmul 19)

theorem integral_norms_etale :
    Etale (integralPi).val ∧ Etale (integralPiConjugate).val := by
  letI : IsFinite (integralPi).val := (integral_norms_finite).1
  letI : IsFinite (integralPiConjugate).val := (integral_norms_finite).2
  letI : FormallyUnramified (integralPi).val :=
    (integral_norms_formallyUnramified).1
  letI : FormallyUnramified (integralPiConjugate).val :=
    (integral_norms_formallyUnramified).2
  letI : Etale ((integralPi).val ≫ (integralPiConjugate).val) := by
    rw [integralPi_comp_integralPiConjugate_eq_local_schemeNsmul]
    exact local_scalar_nineteen_etale
  letI : Etale ((integralPiConjugate).val ≫ (integralPi).val) := by
    rw [integralPiConjugate_comp_integralPi_eq_local_schemeNsmul]
    exact local_scalar_nineteen_etale
  exact ⟨Etale.of_comp (integralPi).val (integralPiConjugate).val,
    Etale.of_comp (integralPiConjugate).val (integralPi).val⟩

theorem integral_norm_fibres_finite_etale {T : Scheme}
    (x : T ⟶ (dyadicPicard).P) :
    (IsFinite (pullback.snd (integralPi).val x) ∧
      Etale (pullback.snd (integralPi).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate).val x) ∧
      Etale (pullback.snd (integralPiConjugate).val x)) := by
  letI : IsFinite (integralPi).val := (integral_norms_finite).1
  letI : IsFinite (integralPiConjugate).val := (integral_norms_finite).2
  letI : Etale (integralPi).val := (integral_norms_etale).1
  letI : Etale (integralPiConjugate).val := (integral_norms_etale).2
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩

end MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormEtale
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormEtale.local_scalar_nineteen_finite_and_flat
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormEtale.local_scalar_nineteen_etale
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormEtale.integral_norms_etale
#print axioms MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormEtale.integral_norm_fibres_finite_etale

end

theorem solution : ((integralPi).val ≫ (integralPiConjugate).val =
      (dyadicLaw).schemeNsmul 19) ∧ ((integralPiConjugate).val ≫ (integralPi).val =
      (dyadicLaw).schemeNsmul 19) ∧ (IsFinite (integralPi).val ∧ IsFinite (integralPiConjugate).val) ∧ (FormallyUnramified (integralPi).val ∧
      FormallyUnramified (integralPiConjugate).val) ∧ (Etale (integralPi).val ∧ Etale (integralPiConjugate).val) ∧ (∀ {T : Scheme}
    (x : T ⟶ (dyadicPicard).P), (IsFinite (pullback.snd (integralPi).val x) ∧
      Etale (pullback.snd (integralPi).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate).val x) ∧
      Etale (pullback.snd (integralPiConjugate).val x))) := by
  exact ⟨MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralScalarNineteen.integralPi_comp_integralPiConjugate_eq_local_schemeNsmul, MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralScalarNineteen.integralPiConjugate_comp_integralPi_eq_local_schemeNsmul, MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormFinite.integral_norms_finite, MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormFinite.integral_norms_formallyUnramified, MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormEtale.integral_norms_etale, MazurTransfer.ScalarNormTheoremBodyV220261019.Order13DyadicMixedIntegralNormEtale.integral_norm_fibres_finite_etale⟩
#print axioms solution
