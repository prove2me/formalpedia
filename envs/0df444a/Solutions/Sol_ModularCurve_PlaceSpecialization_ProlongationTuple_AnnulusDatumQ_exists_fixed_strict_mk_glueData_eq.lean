-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_fixed_strict_mk_glueData_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/37af244b-5129-5512-bc10-99f7ac0966b6

import Mathlib
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_geomAut
import Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support
import Theorems.Thm_ModularCurve_finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_RROpens_exists_forall_hasValue_forall_ord_nonneg
import Theorems.Thm_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_addSubgroup_mem_iff_isGoodClass
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_sum_ord_jGeomGen_sub_eq_dedekindPsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_fixed_strict_mk_glueData_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve~dedekindPsi_pos P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_fixed_strict_mk_glueData_eq.ModularCurve"
open scoped Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv inertiaInvariants mem_inertiaInvariants arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero dedekindPsi ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence nodePairsOfPlaces snd_eq_of_mem_nodePairsOfPlaces ssPlaces jGeomGen jGeomGen_sub_algebraMap_ne_zero arithFrobC PlaceSpecialization.ProlongationTuple.atkinLehnerBar PlaceSpecialization.ProlongationTuple atkinLehnerInvolutionFull frobeniusModL coe_frobeniusModL frobeniusPlaceModL mem_frobeniusPlaceModL_iff NodeLocalized.coeffSubring NodeLocalized.redRestrict jWidth arithmeticGalois_smul_geomAut finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq modularFunctionFieldC_eq_modularFunctionFieldFullC isCurveOver_modularFunctionFieldC_of_perfectField essFiniteType_modularFunctionFieldFullC deg_eq_one_modularFunctionFieldBar isSeparable_jqNModC_of_natCast_ne_zero finite_setOf_ord_jGeomGen_sub_pos sum_ord_jGeomGen_sub_eq_dedekindPsi"
namespace GluedLift
p2m_open "ModularCurve~dedekindPsi_pos"

theorem finite_fixedPoints_iterate_of_eq {K E : Type*} [Field K] [Field E] [Algebra K E]
    {F₁ F₂ : IntermediateField K E} (h : F₁ = F₂)
    (φ₁ : Place K F₁ → Place K F₁) (φ₂ : Place K F₂ → Place K F₂)
    (f₁ : F₁ → F₁) (f₂ : F₂ → F₂)
    (hφ₁ : ∀ (w : Place K F₁) (x : F₁), x ∈ (φ₁ w).toValuationSubring ↔ f₁ x ∈ w.toValuationSubring)
    (hφ₂ : ∀ (w : Place K F₂) (x : F₂), x ∈ (φ₂ w).toValuationSubring ↔ f₂ x ∈ w.toValuationSubring)
    (hf : ∀ (x₁ : F₁) (x₂ : F₂), (x₁ : E) = x₂ → (f₁ x₁ : E) = f₂ x₂)
    (n : ℕ) (hfin : (Function.fixedPoints φ₂^[n]).Finite) :
    (Function.fixedPoints φ₁^[n]).Finite := by
  subst h
  have hφ : φ₁ = φ₂ := by
    funext w
    apply Place.ext
    ext x
    rw [hφ₁, hφ₂, show f₁ x = f₂ x from Subtype.ext (hf x x rfl)]
  rw [hφ]
  exact hfin

theorem semilinearAut_smul_algEquiv_smul {K F : Type*} [Field K] [Field F] [Algebra K F]
    (g : SemilinearAut K F) (σ : F ≃ₐ[K] F) (hcomm : ∀ x : F, g • σ x = σ (g • x))
    (v : Place K F) : g • (σ • v) = σ • (g • v) := by
  apply Place.ext
  ext x
  simp only [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring]
  rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists _ _ _).mp hy
    refine ⟨g • z, ValuationSubring.smul_mem_pointwise_smul g z _ hz, ?_⟩
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, hcomm]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists _ _ _).mp hy
    refine ⟨σ • z, ValuationSubring.smul_mem_pointwise_smul σ z _ hz, ?_⟩
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, hcomm]

theorem isRational_of_isCurveOver {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact hbij.2

theorem degree_single_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (v : Place K F) (n : ℤ) :
    Divisor.degree (Finsupp.single v n) = n := by
  rw [Divisor.degree_single, hdeg v, Nat.cast_one, mul_one]

section LevelN

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem not_isStrictSnd_of_isStrictFst (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (h : P.IsStrictFst W) :
    ¬ P.IsStrictSnd W := by
  rintro ⟨h3, h4⟩
  apply h4
  have h1 := h.1
  rw [h3] at h1
  exact h1

theorem not_isStrictFst_of_isStrictSnd (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (h : P.IsStrictSnd W) :
    ¬ P.IsStrictFst W :=
  fun h' => not_isStrictSnd_of_isStrictFst P h' h

theorem finite_fixedPoints_frobOnPlacesGeomLevel_sq [IsAlgClosed k] (hqN : ¬ q ∣ N) :
    (Function.fixedPoints (frobOnPlacesGeomLevel k N data hKr)^[2]).Finite :=
  finite_fixedPoints_iterate_of_eq
    (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q N hqN)
    (frobOnPlacesGeomLevel k N data hKr) (frobeniusPlaceModL k N q)
    (frobeniusGeomLevel k N data hKr) (frobeniusModL k N q)
    (fun w x => mem_frobOnPlacesGeomLevel_iff k N data hKr w x)
    (fun w x => mem_frobeniusPlaceModL_iff k N q w x)
    (fun x₁ x₂ hx => by rw [frobeniusGeomLevel_apply_coe, coe_frobeniusModL, hx])
    2 (ModularCurve.finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq k N 2 two_pos).1

theorem exists_badFinset [IsAlgClosed k] (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (hqN : ¬ q ∣ N)
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))) :
    ∃ B : Finset (Place k (modularFunctionFieldC k N)),
      (∀ v, v ∉ B → frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v) ∧
      (∀ v, v ∉ B → ∃ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          P.sp u = v ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull N) σ • u = u) ∧
      (∀ s ∈ S, s.1 ∈ B ∧ s.2 ∈ B) := by
  classical
  obtain ⟨X, hX⟩ := P.exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq hqN
  have hfin := finite_fixedPoints_frobOnPlacesGeomLevel_sq (data := data) (hKr := hKr) (k := k) hqN
  refine ⟨X ∪ hfin.toFinset ∪ (S.image Prod.fst ∪ S.image Prod.snd), fun v hv hfix => ?_, fun v hv => ?_,
    fun s hs => ⟨?_, ?_⟩⟩
  · apply hv
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    rw [Set.Finite.mem_toFinset, Function.mem_fixedPoints_iff]
    exact hfix
  · exact hX v (fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs))
  · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs))

theorem arithmeticGalois_smul_atkinLehnerBar_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (PlaceSpecialization.ProlongationTuple.atkinLehnerBar N q • V)
      = PlaceSpecialization.ProlongationTuple.atkinLehnerBar N q • (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) :=
  semilinearAut_smul_algEquiv_smul _ _
    (fun x => ModularCurve.arithmeticGalois_smul_geomAut (AlgebraicClosure ℚ)
      (modularFunctionFieldFull (N * q)) σ (atkinLehnerInvolutionFull N q) x) V

section Lifts

variable (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
  (B : Finset (Place k (modularFunctionFieldC k N)))
  (hB1 : ∀ v, v ∉ B → frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v)
  (hB2 : ∀ v, v ∉ B → ∃ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      P.sp u = v ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull N) σ • u = u)
include hB1 hB2

theorem exists_sndLift (v : Place k (modularFunctionFieldC k N)) (hv : v ∉ B) :
    ∃ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictSnd V ∧ P.reduceSnd V = v ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V := by
  obtain ⟨u, hu, hfix⟩ := hB2 v hv
  have hu2 : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp u)) ≠ P.sp u := by
    rw [hu]; exact hB1 v hv
  obtain ⟨V, hstrict, -, hred, hVfix⟩ :=
    P.exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq u hu2 hfix
  exact ⟨V, hstrict, hred.trans hu, hVfix⟩

include hqN in

theorem exists_fstLift (v : Place k (modularFunctionFieldC k N)) (hv : v ∉ B) :
    ∃ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictFst V ∧ P.reduceFst V = v ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V := by
  obtain ⟨V, hstrict, hred, hVfix⟩ := exists_sndLift P B hB1 hB2 v hv
  have h1 : P.reduceFst (PlaceSpecialization.ProlongationTuple.atkinLehnerBar N q • V) = v := by
    rw [P.reduceFst_atkinLehnerBar_smul hqN V, hred]
  have h2 : P.reduceSnd (PlaceSpecialization.ProlongationTuple.atkinLehnerBar N q • V) = frobOnPlacesGeomLevel k N data hKr v := by
    rw [P.reduceSnd_atkinLehnerBar_smul hqN V, hstrict.1, hred]
  refine ⟨PlaceSpecialization.ProlongationTuple.atkinLehnerBar N q • V, ⟨?_, ?_⟩, h1, fun σ hσ => ?_⟩
  · rw [h1, h2]
  · rw [h1]; exact hB1 v hv
  · rw [arithmeticGalois_smul_atkinLehnerBar_smul, hVfix σ hσ]

end Lifts

def IsGoodLift (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (E₁ E₂ : Divisor k (modularFunctionFieldC k N)) : Prop :=
  P.IsGoodDiv D ∧ Finsupp.mapDomain P.reduceFst (P.fstDiv D) = E₁ ∧
    Finsupp.mapDomain P.reduceSnd (P.sndDiv D) = E₂ ∧
    Divisor.degree D = Divisor.degree E₁ + Divisor.degree E₂ ∧
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • D = D) ∧
    ∀ V ∈ D.support, ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V

theorem isGoodLift_zero (P : PlaceSpecialization A q N data hKr k red hα hβ) : IsGoodLift P 0 0 0 := by
  refine ⟨P.isGoodDiv_zero, ?_, ?_, ?_, fun σ _ => smul_zero _, fun V hV => absurd hV (by simp)⟩
  · rw [P.fstDiv_zero, Finsupp.mapDomain_zero]
  · rw [P.sndDiv_zero, Finsupp.mapDomain_zero]
  · simp only [map_zero, add_zero]

theorem fstDiv_add (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.fstDiv (D + D') = P.fstDiv D + P.fstDiv D' := by
  classical
  unfold PlaceSpecialization.fstDiv
  exact Finsupp.filter_add

theorem sndDiv_add (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.sndDiv (D + D') = P.sndDiv D + P.sndDiv D' := by
  classical
  unfold PlaceSpecialization.sndDiv
  exact Finsupp.filter_add

theorem IsGoodLift.add {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    {E₁ E₂ E₁' E₂' : Divisor k (modularFunctionFieldC k N)}
    (h : IsGoodLift P D E₁ E₂) (h' : IsGoodLift P D' E₁' E₂') :
    IsGoodLift P (D + D') (E₁ + E₁') (E₂ + E₂') := by
  classical
  obtain ⟨hg, h1, h2, hd, hi, hf⟩ := h
  obtain ⟨hg', h1', h2', hd', hi', hf'⟩ := h'
  refine ⟨fun W hW => ?_, ?_, ?_, ?_, fun σ hσ => ?_, fun V hV => ?_⟩
  · rcases Finset.mem_union.mp (Finsupp.support_add hW) with hW | hW
    · exact hg W hW
    · exact hg' W hW
  · rw [fstDiv_add, Finsupp.mapDomain_add, h1, h1']
  · rw [sndDiv_add, Finsupp.mapDomain_add, h2, h2']
  · rw [map_add, map_add, map_add, hd, hd']
    abel
  · rw [smul_add, hi σ hσ, hi' σ hσ]
  · rcases Finset.mem_union.mp (Finsupp.support_add hV) with hV | hV
    · exact hf V hV
    · exact hf' V hV

theorem isGoodLift_single_fst (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (hdeg : ∀ v : Place k (modularFunctionFieldC k N), v.deg = 1)
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hV : P.IsStrictFst V)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V)
    (n : ℤ) :
    IsGoodLift P (Finsupp.single V n) (Finsupp.single (P.reduceFst V) n) 0 := by
  classical
  refine ⟨fun W hW => ?_, ?_, ?_, ?_, fun σ hσ => ?_, fun V' hV' => ?_⟩
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hW)]
    exact Or.inl hV
  · unfold PlaceSpecialization.fstDiv
    rw [Finsupp.filter_single_of_pos _ hV, Finsupp.mapDomain_single]
  · unfold PlaceSpecialization.sndDiv
    rw [Finsupp.filter_single_of_neg _ (not_isStrictSnd_of_isStrictFst P hV), Finsupp.mapDomain_zero]
  · rw [Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) V,
      degree_single_of_deg_eq_one hdeg, map_zero, add_zero, Nat.cast_one, mul_one]
  · rw [SemilinearAut.smul_single, hfix σ hσ]
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hV')]
    exact hfix

theorem isGoodLift_single_snd (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (hdeg : ∀ v : Place k (modularFunctionFieldC k N), v.deg = 1)
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hV : P.IsStrictSnd V)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V)
    (n : ℤ) :
    IsGoodLift P (Finsupp.single V n) 0 (Finsupp.single (P.reduceSnd V) n) := by
  classical
  refine ⟨fun W hW => ?_, ?_, ?_, ?_, fun σ hσ => ?_, fun V' hV' => ?_⟩
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hW)]
    exact Or.inr hV
  · unfold PlaceSpecialization.fstDiv
    rw [Finsupp.filter_single_of_neg _ (not_isStrictFst_of_isStrictSnd P hV), Finsupp.mapDomain_zero]
  · unfold PlaceSpecialization.sndDiv
    rw [Finsupp.filter_single_of_pos _ hV, Finsupp.mapDomain_single]
  · rw [Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) V,
      degree_single_of_deg_eq_one hdeg, map_zero, zero_add, Nat.cast_one, mul_one]
  · rw [SemilinearAut.smul_single, hfix σ hσ]
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hV')]
    exact hfix

section DivisorLift

variable (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
  (B : Finset (Place k (modularFunctionFieldC k N)))
  (hB1 : ∀ v, v ∉ B → frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v)
  (hB2 : ∀ v, v ∉ B → ∃ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      P.sp u = v ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull N) σ • u = u)
include hqN hB1 hB2

theorem exists_isGoodLift_sum_fst (hdeg : ∀ v : Place k (modularFunctionFieldC k N), v.deg = 1)
    (c : Place k (modularFunctionFieldC k N) → ℤ) :
    ∀ s : Finset (Place k (modularFunctionFieldC k N)), (∀ v ∈ s, v ∉ B) →
      ∃ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        IsGoodLift P D (∑ v ∈ s, Finsupp.single v (c v)) 0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, by rw [Finset.sum_empty]; exact isGoodLift_zero P⟩
  | insert a s ha ih =>
    intro hs
    obtain ⟨D, hD⟩ := ih (fun v hv => hs v (Finset.mem_insert_of_mem hv))
    obtain ⟨V, hV, hred, hfix⟩ := exists_fstLift P hqN B hB1 hB2 a (hs a (Finset.mem_insert_self a s))
    refine ⟨Finsupp.single V (c a) + D, ?_⟩
    rw [Finset.sum_insert ha, ← add_zero (0 : Divisor k (modularFunctionFieldC k N))]
    have h1 := isGoodLift_single_fst P hdeg hV hfix (c a)
    rw [hred] at h1
    exact h1.add hD

omit hqN in

theorem exists_isGoodLift_sum_snd (hdeg : ∀ v : Place k (modularFunctionFieldC k N), v.deg = 1)
    (c : Place k (modularFunctionFieldC k N) → ℤ) :
    ∀ s : Finset (Place k (modularFunctionFieldC k N)), (∀ v ∈ s, v ∉ B) →
      ∃ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        IsGoodLift P D 0 (∑ v ∈ s, Finsupp.single v (c v)) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, by rw [Finset.sum_empty]; exact isGoodLift_zero P⟩
  | insert a s ha ih =>
    intro hs
    obtain ⟨D, hD⟩ := ih (fun v hv => hs v (Finset.mem_insert_of_mem hv))
    obtain ⟨V, hV, hred, hfix⟩ := exists_sndLift P B hB1 hB2 a (hs a (Finset.mem_insert_self a s))
    refine ⟨Finsupp.single V (c a) + D, ?_⟩
    rw [Finset.sum_insert ha, ← add_zero (0 : Divisor k (modularFunctionFieldC k N))]
    have h1 := isGoodLift_single_snd P hdeg hV hfix (c a)
    rw [hred] at h1
    exact h1.add hD

theorem exists_isGoodLift (hdeg : ∀ v : Place k (modularFunctionFieldC k N), v.deg = 1)
    (E₁ E₂ : Divisor k (modularFunctionFieldC k N))
    (hE₁ : ∀ v ∈ E₁.support, v ∉ B) (hE₂ : ∀ v ∈ E₂.support, v ∉ B) :
    ∃ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsGoodLift P D E₁ E₂ := by
  obtain ⟨D₁, hD₁⟩ := exists_isGoodLift_sum_fst P hqN B hB1 hB2 hdeg E₁ E₁.support hE₁
  obtain ⟨D₂, hD₂⟩ := exists_isGoodLift_sum_snd P B hB1 hB2 hdeg E₂ E₂.support hE₂
  have h1 : (∑ v ∈ E₁.support, Finsupp.single v (E₁ v)) = E₁ := Finsupp.sum_single E₁
  have h2 : (∑ v ∈ E₂.support, Finsupp.single v (E₂ v)) = E₂ := Finsupp.sum_single E₂
  rw [h1] at hD₁
  rw [h2] at hD₂
  refine ⟨D₁ + D₂, ?_⟩
  have h := hD₁.add hD₂
  rwa [add_zero, zero_add] at h

end DivisorLift

theorem pic0Mk_mem_inertiaInvariants
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hD : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = D) :
    Pic0.mk D ∈ inertiaInvariants A (N * q) := by
  rw [mem_inertiaInvariants]
  intro σ hσ
  rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk]
  congr 1
  exact Subtype.ext (hD σ hσ)

theorem hrat_of_isAlgClosed [IsAlgClosed k] [IsCurveOver k (modularFunctionFieldC k N)]
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))) :
    ∀ s : ↥S,
      Function.Surjective (algebraMap k
        ((s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1.ResidueField)) ∧
      Function.Surjective (algebraMap k
        ((s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).2.ResidueField)) :=
  fun s => ⟨isRational_of_isCurveOver _, isRational_of_isCurveOver _⟩

theorem dedekindPsi_pos (M : ℕ) [NeZero M] : 0 < dedekindPsi M := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ M.divisors.filter (fun d => Squarefree d) :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne M), squarefree_one⟩
  have hle := Finset.single_le_sum (f := fun d => M / d) (fun _ _ => Nat.zero_le _) h1
  have hM : 0 < M / 1 := by rw [Nat.div_one]; exact Nat.pos_of_ne_zero (NeZero.ne M)
  exact lt_of_lt_of_le hM hle

theorem exists_notMem_finset [IsAlgClosed k] (hqN : ¬ q ∣ N)
    (T : Finset (Place k (modularFunctionFieldC k N))) :
    ∃ v : Place k (modularFunctionFieldC k N), v ∉ T := by
  classical
  have hNk : (N : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N).mp h)
  have hsep := ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero k N hNk
  have hex : ∀ a : k, ∃ w : Place k (modularFunctionFieldC k N),
      0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) := by
    intro a
    have hfin := ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k N hsep a
    have hsum := ModularCurve.sum_ord_jGeomGen_sub_eq_dedekindPsi q N hqN k hsep a hfin.toFinset
      (fun w => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq])
    by_contra hne
    push_neg at hne
    have h0 : ∑ w ∈ hfin.toFinset,
        w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) = 0 := by
      refine Finset.sum_eq_zero fun w hw => ?_
      exact absurd ((Set.Finite.mem_toFinset hfin).mp hw) (not_lt.mpr (hne w))
    rw [h0] at hsum
    have hpos := dedekindPsi_pos N
    omega
  choose f hf using hex
  by_contra hall
  push_neg at hall
  obtain ⟨a, a', hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun a : k => (⟨f a, hall (f a)⟩ : ↥T))
  have heq' : f a = f a' := congrArg Subtype.val heq
  apply hne
  have key : ∀ b : k, 0 < (f a).ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) b) →
      (f a).evalAt (jGeomGen k N) = b := by
    intro b hb
    have hmem : jGeomGen k N - algebraMap k (modularFunctionFieldC k N) b ∈ (f a).toValuationSubring :=
      (f a).mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N b) hb.le
    have hj : jGeomGen k N ∈ (f a).toValuationSubring := by
      have := add_mem hmem ((f a).algebraMap_mem' b)
      rwa [sub_add_cancel] at this
    rw [(f a).evalAt_congr hj ((f a).algebraMap_mem' b) (Or.inr hb), (f a).evalAt_algebraMap]
  have hfa' := hf a'
  rw [← heq'] at hfa'
  rw [← key a (hf a), ← key a' hfa']

theorem mk_eq_nodeUnit {K F : Type*} [Field K] [Field F] [Algebra K F]
    (S : Finset (Place K F × Place K F)) (h : F) (hh : h ≠ 0) (Dh : Divisor K F)
    (hDh : ∀ v, Dh v = v.ord h) (b : ↥S → Kˣ)
    (hval : ∀ s : ↥S, (s : Place K F × Place K F).2.HasValue h (b s))
    (hadm : ((0, Dh, 0) : GluingData K F S) ∈ GluingData.admissible S) :
    GluedPic0.mk S ⟨(0, Dh, 0), hadm⟩ = GluedPic0.nodeUnit S (fun s => Additive.ofMul (b s)) := by
  rw [GluedPic0.nodeUnit_apply, GluedPic0.mk_eq_mk_iff]
  refine ⟨1, h⁻¹, 1, fun s => (b s)⁻¹, one_ne_zero, inv_ne_zero hh, fun v => ?_, fun v => ?_,
    fun s => ⟨?_, ?_⟩, ?_⟩
  · simp
  · simp [hDh v, Place.ord_inv]
  · simpa using (s : Place K F × Place K F).1.hasValue_one
  · simpa only [Units.val_inv_eq_inv_val] using (hval s).inv (b s).ne_zero
  · funext s
    simp

section Parts

variable [IsAlgClosed k] (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
  (W : Finset (Place k (modularFunctionFieldC k N)))
include hqN

set_option maxHeartbeats 16000000 in

theorem exists_good_sp_eq_nodeUnit
    (w : ↥(nodePairsOfPlaces (arithFrobC q k N) W) → Additive kˣ) :
    ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
      P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
      (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = D) ∧
      P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) ∧
      ∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W),
        GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W)
          ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩ =
          GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q k N) W) w := by
  classical
  haveI := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  have hdeg : ∀ v : Place k (modularFunctionFieldC k N), v.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  obtain ⟨B, hB1, hB2, hBS⟩ := exists_badFinset P hqN (nodePairsOfPlaces (arithFrobC q k N) W)

  haveI : Algebra.EssFiniteType k ↥(modularFunctionFieldC k N) := by
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q N hqN]
    exact ModularCurve.essFiniteType_modularFunctionFieldFullC k N
  obtain ⟨Kc, g₀, hRR⟩ :=
    AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch k ↥(modularFunctionFieldC k N)
  obtain ⟨P₀, hP₀⟩ := exists_notMem_finset (k := k) hqN B

  set b : ↥(nodePairsOfPlaces (arithFrobC q k N) W) → kˣ := fun s => Additive.toMul (w s) with hb
  set c : Place k (modularFunctionFieldC k N) → k := fun e =>
    if h : ∃ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
        (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).2 = e
    then (b h.choose : k) else 1 with hc
  have hc0 : ∀ e, c e ≠ 0 := by
    intro e
    simp only [hc]
    split_ifs
    · exact Units.ne_zero _
    · exact one_ne_zero
  have hcs : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
      c (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).2 = b s := by
    intro s
    have hex : ∃ s' : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
        (s' : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).2
          = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).2 := ⟨s, rfl⟩
    have hs' : hex.choose = s := by
      have h1 : (hex.choose : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1
          = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 :=
        MulAction.injective (arithFrobC q k N)
          ((snd_eq_of_mem_nodePairsOfPlaces hex.choose.2).symm.trans
            (hex.choose_spec.trans (snd_eq_of_mem_nodePairsOfPlaces s.2)))
      exact Subtype.ext (Prod.ext h1 hex.choose_spec)
    simp only [hc, dif_pos hex, hs']
  obtain ⟨h, hh0, hval, hreg⟩ := AlgebraicCurve.RROpens.exists_forall_hasValue_forall_ord_nonneg
    Kc g₀ hRR B c (fun e _ => hc0 e) P₀ hP₀
  obtain ⟨Dh, hDh, hDh0⟩ := HasPrincipalDivisors.exists_divisor (K := k) h hh0
  have hordB : ∀ v ∈ B, v.ord h = 0 := fun v hv => (hval v hv).ord_eq_zero (hc0 v)
  have hDhB : ∀ v ∈ Dh.support, v ∉ B := fun v hv hvB =>
    (Finsupp.mem_support_iff.mp hv) (by rw [hDh v, hordB v hvB])
  obtain ⟨D, hgood, hfst, hsnd, hdegD, hinv, hfixV⟩ :=
    exists_isGoodLift P hqN B hB1 hB2 hdeg 0 Dh (fun v hv => absurd hv (by simp)) hDhB
  have hD0 : D ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
    rw [Divisor.mem_degZero, hdegD, map_zero, zero_add, hDh0]
  have hadm : ((0, Dh, 0) : GluingData k (modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) :=
    ⟨zero_mem _, Divisor.mem_degZero.mpr hDh0, fun s hs =>
      ⟨rfl, by show Dh s.2 = 0; rw [hDh, hordB _ (hBS s hs).2]⟩⟩
  have hglue : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) D = (0, Dh, 0) :=
    Prod.ext hfst (Prod.ext hsnd rfl)
  have hH : Pic0.mk ⟨D, hD0⟩ ∈ inertiaInvariants A (N * q) := pic0Mk_mem_inertiaInvariants ⟨D, hD0⟩ hinv
  have hadmD : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) := by
    rw [hglue]; exact hadm
  have hw : w = fun s => Additive.ofMul (b s) := by
    funext s
    simp only [hb, ofMul_toMul]
  have hfin : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) ⟨(0, Dh, 0), hadm⟩ =
      GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q k N) W) w := by
    rw [hw]
    exact mk_eq_nodeUnit _ h hh0 Dh hDh b
      (fun s => by rw [← hcs s]; exact hval _ (hBS s s.2).2) hadm
  have hmk : (⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) D, hadmD⟩ :
      ↥(GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W))) = ⟨(0, Dh, 0), hadm⟩ := Subtype.ext hglue
  exact ⟨⟨D, hD0⟩, hgood, hfixV, hinv, hadmD, hadmD,
    (congrArg (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W)) hmk).trans hfin⟩

theorem exists_good_toPic0Pair_sp_eq
    (c : Pic0 k (modularFunctionFieldC k N) × Pic0 k (modularFunctionFieldC k N)) :
    ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
      P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
      (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = D) ∧
      P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) ∧
      ∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W),
        GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q k N) W) (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W)
          ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩) = c := by
  classical
  haveI := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  have hdeg : ∀ v : Place k (modularFunctionFieldC k N), v.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  obtain ⟨B, hB1, hB2, hBS⟩ := exists_badFinset P hqN (nodePairsOfPlaces (arithFrobC q k N) W)
  obtain ⟨E₁, hE₁c, hE₁B⟩ := AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support c.1 B
  obtain ⟨E₂, hE₂c, hE₂B⟩ := AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support c.2 B
  obtain ⟨D, hgood, hfst, hsnd, hdegD, hinv, hfixV⟩ :=
    exists_isGoodLift P hqN B hB1 hB2 hdeg (E₁ : Divisor k (modularFunctionFieldC k N)) E₂ hE₁B hE₂B
  have hD0 : D ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
    rw [Divisor.mem_degZero, hdegD, Divisor.mem_degZero.mp E₁.2, Divisor.mem_degZero.mp E₂.2, add_zero]
  have hadm : (((E₁ : Divisor k (modularFunctionFieldC k N)), (E₂ : Divisor k (modularFunctionFieldC k N)), 0)
        : GluingData k (modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) := by
    refine ⟨E₁.2, E₂.2, fun s hs => ⟨?_, ?_⟩⟩
    · by_contra h
      exact hE₁B _ (Finsupp.mem_support_iff.mpr h) (hBS s hs).1
    · by_contra h
      exact hE₂B _ (Finsupp.mem_support_iff.mpr h) (hBS s hs).2
  have hglue : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) D
      = ((E₁ : Divisor k (modularFunctionFieldC k N)), (E₂ : Divisor k (modularFunctionFieldC k N)), 0) :=
    Prod.ext hfst (Prod.ext hsnd rfl)
  have hH : Pic0.mk ⟨D, hD0⟩ ∈ inertiaInvariants A (N * q) := pic0Mk_mem_inertiaInvariants ⟨D, hD0⟩ hinv
  have hadmD : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) := by
    rw [hglue]; exact hadm
  have hmk : (⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) D, hadmD⟩ :
      ↥(GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W))) = ⟨_, hadm⟩ := Subtype.ext hglue
  have hfin : GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q k N) W)
      (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) ⟨_, hadm⟩) = c := by
    rw [GluedPic0.toPic0Pair_mk]
    exact Prod.ext hE₁c hE₂c
  exact ⟨⟨D, hD0⟩, hgood, hfixV, hinv, hadmD, hadmD,
    (congrArg (fun x => GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q k N) W)
      (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) x)) hmk).trans hfin⟩

end Parts

end LevelN

end ModularCurve.GluedLift

set_option maxHeartbeats 16000000 in
open ModularCurve.GluedLift ModularCurve.PlaceSpecialization in

theorem solution
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumQ W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hwidthj : ∀ w ∈ W, dat.width w = jWidth (w.evalAt (jGeomGen k 1)))
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = dat.depthQ V)
    (hcusp : dat.cusp ∉ W) (hcuspφ : arithFrobC q k 1 • dat.cusp = dat.cusp)
    (hunif : ∀ w ∈ W,
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single w (1 : ℤ) - Finsupp.single dat.cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (dat.unifFst w)) ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single (arithFrobC q k 1 • w) (1 : ℤ) - Finsupp.single dat.cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (dat.unifSnd w)))
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    [hK : ∀ w : Place k (modularFunctionFieldC k 1), FiniteDimensional ℚ ↥(dat.K w)]
    (ϖ : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hϖ : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (eK : Place k (modularFunctionFieldC k 1) → ℕ) (heK : ∀ w ∈ W, 1 ≤ eK w)
    (ε : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (dat.K w))) = ϖ w ^ eK w * ε w)
    (hε1 : ∀ w ∈ W, NodeLocalized.redRestrict red (dat.K w) (ε w) = 1)
    (u : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), IsUnit (u w hw) ∧
        (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w) * u w hw)
    (hmax : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver (dat.K w) w), M.IsMaximal →
          M = Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y})
    (hbr : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x}).IsPrime ∧
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}).IsPrime ∧
        (dat.coord w hw).y ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x} ∧
        (dat.coord w hw).x ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver (dat.K w) w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver (dat.K w) w),
        ∃ o : ↥(NodeLocalized.coeffSubring A (dat.K w)), ¬ IsUnit (g - R.nodeConst (dat.K w) w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (hu0 : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (1 * q))), (u w hw).2.1⟩) ((dat.u0 w : kˣ) : k))
    (hlam : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).y.2.1⟩
        / dat.unifFst w) ((dat.lam w : kˣ) : k))
    (hmu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      (arithFrobC q k 1 • w).HasValue
        (R.nodeResidue₂ w ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).x.2.1⟩
          / dat.unifSnd w) ((dat.mu w : kˣ) : k))
    (g : GluedPic0 k (modularFunctionFieldC k 1) (nodePairsOfPlaces (arithFrobC q k 1) W)) :
    ∃ Dt : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
      (∀ V ∈ (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧
          (P.IsStrictFst V ∨ P.IsStrictSnd V)) ∧
      dat.IsTwistOf ⟨0, 0, fun _ _ => 0⟩ (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∧
      P.IsGoodDiv (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∧
      ∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W),
        GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W) ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩ = g := by
  classical
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  haveI := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k 1
  have hdeg1 : ∀ v : Place k (modularFunctionFieldC k 1), v.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed

  obtain ⟨Dab, hab_good, hab_fix, hab_inv, hab_adm, hadmAb, hab⟩ :=
    exists_good_toPic0Pair_sp_eq P hqN W (GluedPic0.toPic0Pair _ g)

  have hker : g - GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
      ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (Dab : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadmAb⟩ ∈
      (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q k 1) W)).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hab, sub_self]
  rw [AlgebraicCurve.GluedPic0.ker_toPic0Pair_eq_range_nodeUnit _
    (hrat_of_isAlgClosed (k := k) (N := 1) (nodePairsOfPlaces (arithFrobC q k 1) W))] at hker
  obtain ⟨w, hw⟩ := hker

  obtain ⟨Dt, ht_good, ht_fix, ht_inv, ht_adm, hadmT, ht⟩ := exists_good_sp_eq_nodeUnit P hqN W w

  set D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))) := Dab + Dt with hDdef
  have hDcoe : (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) =
      (Dab : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) + Dt := by
    rw [hDdef]; first | rfl | simp | (push_cast; rfl)
  have hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) := by
    rw [hDcoe]
    intro V hV
    rcases Finset.mem_union.mp (Finsupp.support_add hV) with hV | hV
    · exact hab_good V hV
    · exact ht_good V hV
  have hfix : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V := by
    rw [hDcoe]
    intro V hV
    rcases Finset.mem_union.mp (Finsupp.support_add hV) with hV | hV
    · exact hab_fix V hV
    · exact ht_fix V hV
  have hglue : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) =
      P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) Dab + P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) Dt := by
    rw [hDcoe]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show Finsupp.mapDomain P.reduceFst (P.fstDiv (↑Dab + ↑Dt)) = _
      rw [fstDiv_add, Finsupp.mapDomain_add]; rfl
    · show Finsupp.mapDomain P.reduceSnd (P.sndDiv (↑Dab + ↑Dt)) = _
      rw [sndDiv_add, Finsupp.mapDomain_add]; rfl
    · show (0 : ↥(nodePairsOfPlaces (arithFrobC q k 1) W) → Additive kˣ) = 0 + 0
      rw [add_zero]
  have hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W) := by
    rw [hglue]
    exact AddSubgroup.add_mem _ hab_adm ht_adm

  have hcirc : ∀ (w' : Place k (modularFunctionFieldC k 1)) (d : ℕ),
      dat.circleDeg (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w' d = 0 := by
    intro w' d
    unfold ProlongationTuple.AnnulusDatumQ.circleDeg
    refine Finset.sum_eq_zero fun V hV => ?_
    rw [Finset.mem_filter] at hV
    rcases hgood V hV.1 with hs | hs
    · exact absurd hs hV.2.2.1
    · exact absurd hs hV.2.2.2
  have hshareF : ∀ w', dat.endShareFst (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w' = 0 := by
    intro w'
    unfold ProlongationTuple.AnnulusDatumQ.endShareFst
    rw [hcirc]; simp
  have hshareS : ∀ w', dat.endShareSnd (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w' = 0 := by
    intro w'
    unfold ProlongationTuple.AnnulusDatumQ.endShareSnd
    rw [hcirc]; simp
  have hchain0 : ∀ w' d, dat.chainVal (⟨0, 0, fun _ _ => 0⟩ : ProlongationTuple.TwistVector (k := k) W) w' d = 0 := by
    intro w' d
    unfold ProlongationTuple.AnnulusDatumQ.chainVal
    split_ifs <;> rfl
  have hdegMap : ∀ (f : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Place k ↥(modularFunctionFieldC k 1))
      (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      Divisor.degree (Finsupp.mapDomain f E) = Divisor.degree E := by
    intro f E
    induction E using Finsupp.induction with
    | zero => simp
    | single_add V n E _ _ ih =>
      rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_add, map_add, ih, Divisor.degree_single,
        Divisor.degree_single, hdeg1, ModularCurve.deg_eq_one_modularFunctionFieldBar (1 * q) V]
  obtain ⟨hadm1, hadm2, -⟩ := (show _ ∧ _ ∧ _ from hadm)
  have hdegF : Divisor.degree (P.fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) = 0 := by
    rw [← hdegMap P.reduceFst]; exact Divisor.mem_degZero.mp hadm1
  have hdegS : Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) = 0 := by
    rw [← hdegMap P.reduceSnd]; exact Divisor.mem_degZero.mp hadm2
  have htwist : dat.IsTwistOf ⟨0, 0, fun _ _ => 0⟩ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hdegF]
      symm
      rw [neg_eq_zero]
      refine Finset.sum_eq_zero fun w' _ => ?_
      unfold ProlongationTuple.AnnulusDatumQ.endOrderFst ProlongationTuple.AnnulusDatumQ.endSlopeFst
      rw [hchain0, hchain0, hshareF]; simp
    · rw [hdegS]
      symm
      rw [neg_eq_zero]
      refine Finset.sum_eq_zero fun w' _ => ?_
      unfold ProlongationTuple.AnnulusDatumQ.endOrderSnd ProlongationTuple.AnnulusDatumQ.endSlopeSnd
      rw [hchain0, hchain0, hshareS]; simp
    · intro w' _ d _ _
      rw [hcirc, hchain0, hchain0, hchain0]; simp

  have hmk : (⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩ :
        ↥(GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))) =
      ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (Dab : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadmAb⟩ +
        ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadmT⟩ := by
    apply Subtype.ext
    first | exact hglue | (simp only [AddSubgroup.coe_add, AddMemClass.coe_add]; exact hglue) | (show _ = _ + _; exact hglue)
  have hfinal : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
      (⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (Dab : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadmAb⟩ +
        ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadmT⟩) = g := by
    rw [map_add, ht, hw]
    abel
  exact ⟨D, fun V hV => ⟨hfix V hV, hgood V hV⟩, htwist, hgood, hadm,
    (congrArg (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)) hmk).trans hfinal⟩

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_fixed_strict_mk_glueData_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_fixed_strict_mk_glueData_eq (solution)
