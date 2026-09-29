-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8dcb9d47-33a1-5e6d-9533-743c325221f9

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Theorems.Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_minpoly_jqNModC_eq
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ValuationSubring_exists_algEquiv_forall_mem_iff_of_nonunits
import Theorems.Thm_ValuationSubring_exists_algEquiv_residue_pow_eq_of_nonunits
import Theorems.Thm_ValuationSubring_finite_range_residue_of_nonunits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

def coeffValuationSubring : ValuationSubring K where
  carrier := {x | (x : AlgebraicClosure ℚ) ∈ A}
  mul_mem' hx hy := A.mul_mem _ _ hx hy
  one_mem' := A.one_mem
  add_mem' hx hy := A.add_mem _ _ hx hy
  zero_mem' := A.zero_mem
  neg_mem' hx := A.neg_mem _ hx
  mem_or_inv_mem' x := A.mem_or_inv_mem (x : AlgebraicClosure ℚ)

theorem mem_coeffValuationSubring {x : K} :
    x ∈ coeffValuationSubring A K ↔ (x : AlgebraicClosure ℚ) ∈ A :=
  Iff.rfl

theorem mem_coeffSubring {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K :=
  Iff.rfl

def coeffSubringEquiv : coeffSubring A K ≃+* coeffValuationSubring A K where
  toFun x := ⟨⟨(x : AlgebraicClosure ℚ), ((mem_coeffSubring A K).mp x.2).2⟩,
    ((mem_coeffSubring A K).mp x.2).1⟩
  invFun v := ⟨((v : K) : AlgebraicClosure ℚ), (mem_coeffSubring A K).mpr ⟨v.2, (v : K).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem mem_of_isIntegral_int {x : AlgebraicClosure ℚ} (hx : IsIntegral ℤ x) : x ∈ A := by

  have hA : IsIntegral A x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap A (AlgebraicClosure ℚ)).comp (Int.castRingHom A)) (algebraMap ℤ _)]
    exact hpx
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hA
  rw [← hz]
  exact z.2

theorem blockB [FiniteDimensional ℚ K] :
    IsNoetherianRing ↥(coeffSubring A K) ∧ IsIntegrallyClosed ↥(coeffSubring A K) ∧
      IsDomain ↥(coeffSubring A K) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : NumberField K := NumberField.mk

  have hOV : ∀ r : NumberField.RingOfIntegers K,
      algebraMap (NumberField.RingOfIntegers K) K r ∈ coeffValuationSubring A K := by
    intro r
    rw [mem_coeffValuationSubring]
    have hint : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K r) :=
      NumberField.RingOfIntegers.isIntegral_coe r

    apply mem_of_isIntegral_int A
    obtain ⟨p, hp, hpr⟩ := hint
    refine ⟨p, hp, ?_⟩
    have h := congrArg (IntermediateField.val K).toRingHom hpr
    rw [map_zero, Polynomial.hom_eval₂,
      RingHom.ext_int (RingHom.comp _ _) (algebraMap ℤ (AlgebraicClosure ℚ))] at h
    exact h

  have hnoeth : IsNoetherianRing (coeffValuationSubring A K) := by
    by_cases hV : coeffValuationSubring A K = ⊤
    · have e' : (coeffValuationSubring A K).toSubring ≃+* K :=
        (RingEquiv.subringCongr (by rw [hV]; rfl)).trans Subring.topEquiv
      exact isNoetherianRing_of_ringEquiv K e'.symm
    · obtain ⟨v, hv, -⟩ :=
        ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
          (coeffValuationSubring A K) hOV hV
      rw [hv]
      infer_instance
  refine ⟨isNoetherianRing_of_ringEquiv _ (coeffSubringEquiv A K).symm,
    IsIntegrallyClosed.of_equiv (coeffSubringEquiv A K).symm, inferInstance⟩

end

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section

open Polynomial

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

def jEval : Polynomial (coeffSubring A K) →+* LaurentSeries (AlgebraicClosure ℚ) :=
  Polynomial.eval₂RingHom (CharPReduction.constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ))

theorem jEval_apply (p : Polynomial (coeffSubring A K)) :
    jEval A K p = p.eval₂ (CharPReduction.constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ)) :=
  rfl

theorem constSeries_eq_comp :
    CharPReduction.constSeries (coeffSubring A K)
      = (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp
          (coeffSubring A K).subtype :=
  rfl

theorem jEval_eq_aeval_map (p : Polynomial (coeffSubring A K)) :
    jEval A K p = Polynomial.aeval (jqModC (AlgebraicClosure ℚ)) (p.map (coeffSubring A K).subtype) := by
  rw [jEval_apply, Polynomial.aeval_def, Polynomial.eval₂_map, constSeries_eq_comp]

theorem jEval_injective : Function.Injective (jEval A K) := by
  intro p q h
  rw [jEval_eq_aeval_map, jEval_eq_aeval_map] at h
  have hinj : Function.Injective (Polynomial.aeval (R := AlgebraicClosure ℚ) (jqModC (AlgebraicClosure ℚ))) :=
    transcendental_iff_injective.mp (ModularCurve.transcendental_jqModC (AlgebraicClosure ℚ))
  exact Polynomial.map_injective _ Subtype.val_injective (hinj h)

theorem range_jEval : (jEval A K).range = jRing A K := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a =>
        rw [jEval_apply, Polynomial.eval₂_monomial]
        have h1 : CharPReduction.constSeries (coeffSubring A K) a ∈ jRing A K :=
          Subring.subset_closure (Or.inl ⟨a, rfl⟩)
        have h2 : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
          Subring.subset_closure (Or.inr rfl)
        exact (jRing A K).mul_mem h1 ((jRing A K).pow_mem h2 n)
  · rw [jRing, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · exact ⟨Polynomial.C a, by rw [jEval_apply, Polynomial.eval₂_C]⟩
    · exact ⟨Polynomial.X, by rw [jEval_apply, Polynomial.eval₂_X]⟩

def polynomialEquivJRing : Polynomial (coeffSubring A K) ≃+* jRing A K :=
  (RingEquiv.ofBijective (jEval A K).rangeRestrict
      ⟨fun _ _ h => jEval_injective A K (congrArg Subtype.val h),
        (jEval A K).rangeRestrict_surjective⟩).trans
    (RingEquiv.subringCongr (range_jEval A K))

theorem coe_polynomialEquivJRing (p : Polynomial (coeffSubring A K)) :
    ((polynomialEquivJRing A K p : jRing A K) : LaurentSeries (AlgebraicClosure ℚ))
      = p.eval₂ (CharPReduction.constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ)) :=
  rfl

theorem exists_polynomial_equiv_jRing :
    ∃ e : Polynomial ↥(coeffSubring A K) ≃+* ↥(jRing A K),
      ∀ p, ((e p : ↥(jRing A K)) : LaurentSeries (AlgebraicClosure ℚ))
        = p.eval₂ (CharPReduction.constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ)) :=
  ⟨polynomialEquivJRing A K, coe_polynomialEquivJRing A K⟩

end

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem mem_coeffSubring_iff {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := by
  simp only [coeffSubring, Subring.mem_inf]
  exact Iff.rfl

theorem exists_div_eq_of_mem' (x : AlgebraicClosure ℚ) (hx : x ∈ K) :
    ∃ a b : ↥(coeffSubring A K), (b : AlgebraicClosure ℚ) ≠ 0 ∧ x = a / b := by
  rcases A.mem_or_inv_mem x with h | h
  · refine ⟨⟨x, (mem_coeffSubring_iff A K).mpr ⟨h, hx⟩⟩, ⟨1, one_mem _⟩, ?_, ?_⟩
    · simp
    · simp
  · by_cases hx0 : x = 0
    · refine ⟨⟨0, zero_mem _⟩, ⟨1, one_mem _⟩, by simp, by simp [hx0]⟩
    refine ⟨⟨1, one_mem _⟩, ⟨x⁻¹, (mem_coeffSubring_iff A K).mpr ⟨h, IntermediateField.inv_mem K hx⟩⟩, ?_, ?_⟩
    · simpa using hx0
    · simp

theorem constSeries_coeffSubring_apply (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) := rfl

theorem algebraMap_mem_fieldOver (N : ℕ) [NeZero N] {x : AlgebraicClosure ℚ} (hx : x ∈ K) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) x ∈ fieldOver N K := by
  refine Subfield.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem jqModC_mem_fieldOver (N : ℕ) [NeZero N] : jqModC (AlgebraicClosure ℚ) ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem jqNModC_mem_fieldOver' (N : ℕ) [NeZero N] : jqNModC (AlgebraicClosure ℚ) N ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

theorem jqModC_mem_jRing' : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
  Subring.subset_closure (Or.inr rfl)

theorem constSeries_mem_jRing (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem jRing_le_fieldOver' (N : ℕ) [NeZero N] : jRing A K ≤ (fieldOver N K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact algebraMap_mem_fieldOver K N ((mem_coeffSubring_iff A K).mp a.2).2
  · exact jqModC_mem_fieldOver K N

theorem fieldOver_eq_closure' (N : ℕ) [NeZero N] :
    fieldOver N K = Subfield.closure ((jRing A K : Set (LaurentSeries (AlgebraicClosure ℚ)))
      ∪ {jqNModC (AlgebraicClosure ℚ) N}) := by
  apply le_antisymm
  · rw [fieldOver, Subfield.closure_le]
    rintro x (⟨a, rfl⟩ | rfl | rfl)
    ·
      obtain ⟨b, c, hc, hbc⟩ := exists_div_eq_of_mem' A K (a : AlgebraicClosure ℚ) a.2
      have : CharPReduction.constSeries K.toSubalgebra.toSubring a
          = CharPReduction.constSeries (coeffSubring A K) b / CharPReduction.constSeries (coeffSubring A K) c := by
        show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) = _
        rw [hbc, map_div₀]; rfl
      rw [this]
      exact div_mem (Subfield.subset_closure (Or.inl (constSeries_mem_jRing A K b)))
        (Subfield.subset_closure (Or.inl (constSeries_mem_jRing A K c)))
    · exact Subfield.subset_closure (Or.inl (jqModC_mem_jRing' A K))
    · exact Subfield.subset_closure (Or.inr rfl)
  · rw [Subfield.closure_le]
    rintro x (hx | rfl)
    · exact jRing_le_fieldOver' A K N hx
    · exact jqNModC_mem_fieldOver' K N

theorem isIntegral_jRing_jqNModC' (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral ↥(jRing A K) (jqNModC (AlgebraicClosure ℚ) N) := by
  let jR : ↥(jRing A K) := ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_jRing' A K⟩
  refine ⟨data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(jRing A K)) jR), data.monic.map _, ?_⟩

  let F := IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))
  let jF : ↥F := ⟨jqModC (AlgebraicClosure ℚ), IntermediateField.mem_adjoin_simple_self _ _⟩
  have h0 : Polynomial.aeval (jqNModC (AlgebraicClosure ℚ) N) (minpoly ↥F (jqNModC (AlgebraicClosure ℚ) N)) = 0 :=
    minpoly.aeval ↥F _
  rw [ModularCurve.minpoly_jqNModC_eq (AlgebraicClosure ℚ) N data, Polynomial.aeval_def,
    Polynomial.eval₂_map] at h0
  rw [Polynomial.eval₂_map]
  convert h0 using 2 <;> try rfl
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [jR, jF]
  rfl

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A₀ : Subring L) {k : Type*} [Field k]
  (red : A₀ →+* k) (a b : k)

def modularRange : Subring (LaurentSeries L) := (modularEval N A₀).range

theorem modularEval_mem_modularRange (p : MvPolynomial (Fin 2) A₀) :
    modularEval N A₀ p ∈ modularRange N A₀ :=
  ⟨p, rfl⟩

theorem mem_modularRange_iff {x : LaurentSeries L} :
    x ∈ modularRange N A₀ ↔ ∃ p : MvPolynomial (Fin 2) A₀, modularEval N A₀ p = x :=
  Iff.rfl

theorem modularRange_le_modularLocalizedAtPoint :
    modularRange N A₀ ≤ modularLocalizedAtPoint N A₀ red a b := by
  rintro _ ⟨p, rfl⟩
  exact modularEval_mem_modularLocalizedAtPoint N A₀ red a b p

def nodeUnits : Submonoid (modularRange N A₀) where
  carrier := {m | ∃ s : MvPolynomial (Fin 2) A₀, pointEval A₀ red a b s ≠ 0 ∧
    (m : LaurentSeries L) = modularEval N A₀ s}
  one_mem' := ⟨1, by rw [map_one]; exact one_ne_zero, by rw [map_one]; rfl⟩
  mul_mem' := by
    rintro m m' ⟨s, hs, hm⟩ ⟨t, ht, hm'⟩
    refine ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [map_mul, ← hm, ← hm']
    rfl

theorem mem_nodeUnits_iff {m : modularRange N A₀} :
    m ∈ nodeUnits N A₀ red a b ↔ ∃ s : MvPolynomial (Fin 2) A₀, pointEval A₀ red a b s ≠ 0 ∧
      (m : LaurentSeries L) = modularEval N A₀ s :=
  Iff.rfl

def nodeUnitOf (s : MvPolynomial (Fin 2) A₀) (hs : pointEval A₀ red a b s ≠ 0) :
    nodeUnits N A₀ red a b :=
  ⟨⟨modularEval N A₀ s, modularEval_mem_modularRange N A₀ s⟩, s, hs, rfl⟩

@[reducible] def modularRangeAlgebra : Algebra (modularRange N A₀) (modularLocalizedAtPoint N A₀ red a b) :=
  (Subring.inclusion (modularRange_le_modularLocalizedAtPoint N A₀ red a b)).toAlgebra

attribute [local instance] modularRangeAlgebra

theorem algebraMap_modularRange_apply (x : modularRange N A₀) :
    ((algebraMap (modularRange N A₀) (modularLocalizedAtPoint N A₀ red a b) x :
      modularLocalizedAtPoint N A₀ red a b) : LaurentSeries L) = x :=
  rfl

theorem isScalarTower_modularRange :
    IsScalarTower (modularRange N A₀) (modularLocalizedAtPoint N A₀ red a b) (LaurentSeries L) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] isScalarTower_modularRange

theorem isLocalization_nodeUnits
    (hM : ∀ s : MvPolynomial (Fin 2) A₀, pointEval A₀ red a b s ≠ 0 → modularEval N A₀ s ≠ 0) :
    IsLocalization (nodeUnits N A₀ red a b) (modularLocalizedAtPoint N A₀ red a b) where
  map_units := by
    rintro ⟨m, s, hs, hm⟩
    have hm0 : (m : LaurentSeries L) ≠ 0 := by rw [hm]; exact hM s hs

    have hinv : (m : LaurentSeries L)⁻¹ ∈ modularLocalizedAtPoint N A₀ red a b :=
      ⟨1, s, hs, by rw [← hm, inv_mul_cancel₀ hm0, map_one]⟩
    refine IsUnit.of_mul_eq_one ⟨(m : LaurentSeries L)⁻¹, hinv⟩ ?_
    apply Subtype.ext
    change (m : LaurentSeries L) * (m : LaurentSeries L)⁻¹ = 1
    exact mul_inv_cancel₀ hm0
  surj := by
    rintro ⟨z, r, s, hs, hz⟩
    refine ⟨(⟨modularEval N A₀ r, modularEval_mem_modularRange N A₀ r⟩, nodeUnitOf N A₀ red a b s hs), ?_⟩
    apply Subtype.ext
    exact hz
  exists_of_eq := by
    intro x y h
    refine ⟨1, ?_⟩
    have : (x : LaurentSeries L) = y := congrArg (fun z : modularLocalizedAtPoint N A₀ red a b => (z : LaurentSeries L)) h
    rw [Subtype.ext this]

theorem exists_nodeUnit_mul_isIntegral
    (hM : ∀ s : MvPolynomial (Fin 2) A₀, pointEval A₀ red a b s ≠ 0 → modularEval N A₀ s ≠ 0)
    (x : LaurentSeries L) (hx : IsIntegral (modularLocalizedAtPoint N A₀ red a b) x) :
    ∃ s : MvPolynomial (Fin 2) A₀, pointEval A₀ red a b s ≠ 0 ∧
      IsIntegral (modularRange N A₀) (x * modularEval N A₀ s) := by
  haveI := isLocalization_nodeUnits N A₀ red a b hM
  obtain ⟨m, hm⟩ := hx.exists_multiple_integral_of_isLocalization (nodeUnits N A₀ red a b)
  obtain ⟨s, hs, hms⟩ := m.2
  refine ⟨s, hs, ?_⟩
  rw [Submonoid.smul_def, Algebra.smul_def, mul_comm] at hm
  rwa [← hms]

end

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem modularEval_mem_fieldOver (N : ℕ) [NeZero N] (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    modularEval N (coeffSubring A K) p ∈ fieldOver N K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_C]
      exact algebraMap_mem_fieldOver K N ((mem_coeffSubring_iff A K).mp c.2).2
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact jqModC_mem_fieldOver K N
      · exact jqNModC_mem_fieldOver' K N

theorem jRing_le_modularLocalizedAtPoint (N : ℕ) [NeZero N] {k : Type*} [Field k]
    (red₀ : ↥(coeffSubring A K) →+* k) (a b : k) :
    jRing A K ≤ modularLocalizedAtPoint N (coeffSubring A K) red₀ a b := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨c, rfl⟩ | rfl)
  · have : CharPReduction.constSeries (coeffSubring A K) c = modularEval N (coeffSubring A K) (MvPolynomial.C c) := by
      unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
    rw [this]
    exact modularEval_mem_modularLocalizedAtPoint N _ red₀ a b _
  · have : jqModC (AlgebraicClosure ℚ) = modularEval N (coeffSubring A K) (MvPolynomial.X 0) := by
      unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl
    rw [this]
    exact modularEval_mem_modularLocalizedAtPoint N _ red₀ a b _

theorem isIntegral_modularLocalizedAtPoint_of_isIntegral_jRing (N : ℕ) [NeZero N] {k : Type*} [Field k]
    (red₀ : ↥(coeffSubring A K) →+* k) (a b : k) {c : LaurentSeries (AlgebraicClosure ℚ)}
    (hc : IsIntegral ↥(jRing A K) c) :
    IsIntegral ↥(modularLocalizedAtPoint N (coeffSubring A K) red₀ a b) c := by
  have hle := jRing_le_modularLocalizedAtPoint A K N red₀ a b
  obtain ⟨p, hp, hpc⟩ := hc
  refine ⟨p.map (Subring.inclusion hle), hp.map _, ?_⟩
  have hcomp : (algebraMap ↥(modularLocalizedAtPoint N (coeffSubring A K) red₀ a b)
      (LaurentSeries (AlgebraicClosure ℚ))).comp (Subring.inclusion hle)
        = algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) :=
    RingHom.ext fun _ => rfl
  rw [Polynomial.eval₂_map, hcomp]
  exact hpc

theorem mem_fieldOver_and_isIntegral_of_mul_modularEval_eq (N : ℕ) [NeZero N] {k : Type*} [Field k]
    (red₀ : ↥(coeffSubring A K) →+* k) (a b : k)
    (hM : ∀ s, pointEval (coeffSubring A K) red₀ a b s ≠ 0 → modularEval N (coeffSubring A K) s ≠ 0)
    {x c : LaurentSeries (AlgebraicClosure ℚ)} (hc : c ∈ jIntegralClosure N A K)
    {s : MvPolynomial (Fin 2) ↥(coeffSubring A K)} (hs : pointEval (coeffSubring A K) red₀ a b s ≠ 0)
    (hx : x * modularEval N (coeffSubring A K) s = c) :
    x ∈ fieldOver N K ∧ IsIntegral ↥(modularLocalizedAtPoint N (coeffSubring A K) red₀ a b) x := by
  have hs0 : modularEval N (coeffSubring A K) s ≠ 0 := hM s hs
  have hxeq : x = c * (modularEval N (coeffSubring A K) s)⁻¹ := by
    rw [← hx, mul_inv_cancel_right₀ hs0]

  have hinv : (modularEval N (coeffSubring A K) s)⁻¹ ∈ modularLocalizedAtPoint N (coeffSubring A K) red₀ a b :=
    ⟨1, s, hs, by rw [inv_mul_cancel₀ hs0, map_one]⟩
  refine ⟨?_, ?_⟩
  · rw [hxeq]
    exact mul_mem hc.1 (inv_mem (modularEval_mem_fieldOver A K N s))
  · rw [hxeq]
    refine IsIntegral.mul (isIntegral_modularLocalizedAtPoint_of_isIntegral_jRing A K N red₀ a b hc.2) ?_
    exact isIntegral_algebraMap (R := ↥(modularLocalizedAtPoint N (coeffSubring A K) red₀ a b))
      (A := LaurentSeries (AlgebraicClosure ℚ)) (x := ⟨_, hinv⟩)

end

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (N : ℕ) [NeZero N]

theorem jRing_le_modularRange : jRing A K ≤ modularRange N (coeffSubring A K) := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨c, rfl⟩ | rfl)
  · refine ⟨MvPolynomial.C c, ?_⟩
    unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
  · refine ⟨MvPolynomial.X 0, ?_⟩
    unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl

@[reducible] def jRingModularRangeAlgebra : Algebra ↥(jRing A K) ↥(modularRange N (coeffSubring A K)) :=
  (Subring.inclusion (jRing_le_modularRange A K N)).toAlgebra

attribute [local instance] jRingModularRangeAlgebra

theorem isScalarTower_jRing_modularRange :
    IsScalarTower ↥(jRing A K) ↥(modularRange N (coeffSubring A K)) (LaurentSeries (AlgebraicClosure ℚ)) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] isScalarTower_jRing_modularRange

theorem isIntegral_jRing_modularEval (data : ModularPolynomialData N)
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    IsIntegral ↥(jRing A K) (modularEval N (coeffSubring A K) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_C]
      exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, constSeries_mem_jRing A K c⟩)
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
      rw [map_mul]
      refine hp.mul ?_
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, jqModC_mem_jRing' A K⟩)
      · exact isIntegral_jRing_jqNModC' A K N data

theorem algebra_isIntegral_jRing_modularRange (data : ModularPolynomialData N) :
    Algebra.IsIntegral ↥(jRing A K) ↥(modularRange N (coeffSubring A K)) := by
  refine ⟨fun m => ?_⟩
  obtain ⟨p, hp⟩ := (mem_modularRange_iff N (coeffSubring A K)).mp m.2
  have h : IsIntegral ↥(jRing A K)
      ((IsScalarTower.toAlgHom ↥(jRing A K) ↥(modularRange N (coeffSubring A K))
        (LaurentSeries (AlgebraicClosure ℚ))) m) := by
    change IsIntegral ↥(jRing A K) (m : LaurentSeries (AlgebraicClosure ℚ))
    rw [← hp]
    exact isIntegral_jRing_modularEval A K N data p
  exact (isIntegral_algHom_iff _ Subtype.val_injective).mp h

theorem isIntegral_jRing_of_isIntegral_modularRange (data : ModularPolynomialData N)
    {y : LaurentSeries (AlgebraicClosure ℚ)}
    (hy : IsIntegral ↥(modularRange N (coeffSubring A K)) y) :
    IsIntegral ↥(jRing A K) y := by
  haveI := algebra_isIntegral_jRing_modularRange A K N data
  exact isIntegral_trans y hy

end

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

scoped instance charZero_laurentSeries_algClosure : CharZero (LaurentSeries (AlgebraicClosure ℚ)) :=
  charZero_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := AlgebraicClosure ℚ))

scoped instance charZero_fieldOver (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    CharZero ↥(fieldOver N K) :=
  (fieldOver N K).subtype.charZero

end NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

open Polynomial

section Tower

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (N : ℕ) [NeZero N]

def jRingToFieldOver : ↥(jRing A K) →+* ↥(fieldOver N K) where
  toFun x := ⟨x, jRing_le_fieldOver' A K N x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

set_option maxHeartbeats 12800000 in
noncomputable scoped instance algebraJRingFieldOver : Algebra ↥(jRing A K) ↥(fieldOver N K) :=
  (jRingToFieldOver A K N).toAlgebra

set_option maxHeartbeats 12800000 in
scoped instance isScalarTower_jRing_fieldOver :
    IsScalarTower ↥(jRing A K) ↥(fieldOver N K) (LaurentSeries (AlgebraicClosure ℚ)) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

set_option maxHeartbeats 12800000 in
theorem jRingToFieldOver_injective : Function.Injective (jRingToFieldOver A K N) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg (fun z : ↥(fieldOver N K) => (z : LaurentSeries (AlgebraicClosure ℚ))) h
  exact h'

set_option maxHeartbeats 12800000 in
scoped instance faithfulSMul_jRing_fieldOver : FaithfulSMul ↥(jRing A K) ↥(fieldOver N K) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (jRingToFieldOver_injective A K N)

noncomputable def jN : ↥(fieldOver N K) := ⟨jqNModC (AlgebraicClosure ℚ) N, jqNModC_mem_fieldOver' K N⟩

theorem isIntegral_jRing_jN (data : ModularPolynomialData N) : IsIntegral ↥(jRing A K) (jN K N) :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(jRing A K) ↥(fieldOver N K) (LaurentSeries (AlgebraicClosure ℚ)))
    Subtype.val_injective).mp (isIntegral_jRing_jqNModC' A K N data)

set_option maxHeartbeats 6400000 in

theorem adjoin_jN_eq_top (F : Type*) [Field F] [Algebra ↥(jRing A K) F] [Algebra F ↥(fieldOver N K)]
    [IsScalarTower ↥(jRing A K) F ↥(fieldOver N K)] :
    IntermediateField.adjoin F ({jN K N} : Set ↥(fieldOver N K)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have hx' : x ∈ Subfield.closure ((jRing A K : Set (LaurentSeries (AlgebraicClosure ℚ)))
      ∪ {jqNModC (AlgebraicClosure ℚ) N}) := by rwa [← fieldOver_eq_closure' A K N]

  induction hx' using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with hy | rfl
    · have : (⟨y, hx⟩ : ↥(fieldOver N K)) = algebraMap F _ (algebraMap ↥(jRing A K) F ⟨y, hy⟩) := by
        rw [← IsScalarTower.algebraMap_apply]; rfl
      rw [this]; exact IntermediateField.algebraMap_mem _ _
    · exact IntermediateField.subset_adjoin F _ (Set.mem_singleton _)
  | one =>
    have e : (⟨1, hx⟩ : ↥(fieldOver N K)) = 1 := Subtype.ext rfl
    rw [e]; exact one_mem _
  | add y z hy hz ihy ihz =>
    have hyF : y ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hy
    have hzF : z ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hz
    have e : (⟨y + z, hx⟩ : ↥(fieldOver N K)) = (⟨y, hyF⟩ : ↥(fieldOver N K)) + ⟨z, hzF⟩ := Subtype.ext rfl
    rw [e]
    exact add_mem (ihy hyF) (ihz hzF)
  | neg y hy ihy =>
    have hyF : y ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hy
    have e : (⟨-y, hx⟩ : ↥(fieldOver N K)) = -(⟨y, hyF⟩ : ↥(fieldOver N K)) := Subtype.ext rfl
    rw [e]
    exact neg_mem (ihy hyF)
  | inv y hy ihy =>
    have hyF : y ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hy
    have e : (⟨y⁻¹, hx⟩ : ↥(fieldOver N K)) = (⟨y, hyF⟩ : ↥(fieldOver N K))⁻¹ := Subtype.ext rfl
    rw [e]
    exact inv_mem (ihy hyF)
  | mul y z hy hz ihy ihz =>
    have hyF : y ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hy
    have hzF : z ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hz
    have e : (⟨y * z, hx⟩ : ↥(fieldOver N K)) = (⟨y, hyF⟩ : ↥(fieldOver N K)) * ⟨z, hzF⟩ := Subtype.ext rfl
    rw [e]
    exact mul_mem (ihy hyF) (ihz hzF)

def jRingToIntegralClosure : ↥(jRing A K) →+* ↥(jIntegralClosure N A K) where
  toFun x := ⟨x, jRing_le_fieldOver' A K N x.2, isIntegral_algebraMap (R := ↥(jRing A K)) (x := x)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def integralClosureToFieldOver : ↥(jIntegralClosure N A K) →+* ↥(fieldOver N K) where
  toFun x := ⟨x, x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable scoped instance algebraJRingIntegralClosure : Algebra ↥(jRing A K) ↥(jIntegralClosure N A K) :=
  (jRingToIntegralClosure A K N).toAlgebra

noncomputable scoped instance algebraIntegralClosureFieldOver : Algebra ↥(jIntegralClosure N A K) ↥(fieldOver N K) :=
  (integralClosureToFieldOver A K N).toAlgebra

set_option maxHeartbeats 12800000 in
scoped instance isScalarTower_jRing_integralClosure_fieldOver :
    IsScalarTower ↥(jRing A K) ↥(jIntegralClosure N A K) ↥(fieldOver N K) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

set_option maxHeartbeats 12800000 in
scoped instance isIntegralClosure_jIntegralClosure :
    IsIntegralClosure ↥(jIntegralClosure N A K) ↥(jRing A K) ↥(fieldOver N K) where
  algebraMap_injective x y h := Subtype.ext (congrArg (fun z : ↥(fieldOver N K) => (z : LaurentSeries (AlgebraicClosure ℚ))) h)
  isIntegral_iff {x} := by
    constructor
    · intro hx
      have hx' : IsIntegral ↥(jRing A K) (x : LaurentSeries (AlgebraicClosure ℚ)) :=
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(jRing A K) ↥(fieldOver N K)
          (LaurentSeries (AlgebraicClosure ℚ))) Subtype.val_injective).mpr hx
      exact ⟨⟨x, x.2, hx'⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(jRing A K) ↥(fieldOver N K)
          (LaurentSeries (AlgebraicClosure ℚ))) Subtype.val_injective).mp y.2.2

end Tower
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

end NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section
p2m_open "ModularCurve.CharPReduction"

section Vocab

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem mem_coeffSubring_iff' {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := Iff.rfl

theorem algebraMap_mem_fieldOver' (N : ℕ) [NeZero N] {x : AlgebraicClosure ℚ} (hx : x ∈ K) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) x ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem jqModC_mem_fieldOver' (N : ℕ) [NeZero N] : jqModC (AlgebraicClosure ℚ) ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem jqNModC_mem_fieldOver'' (N : ℕ) [NeZero N] : jqNModC (AlgebraicClosure ℚ) N ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

theorem jqModC_mem_jRing'' : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
  Subring.subset_closure (Or.inr rfl)

theorem constSeries_mem_jRing' (a : ↥(coeffSubring A K)) :
    constSeries (coeffSubring A K) a ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem modularEval_mem_fieldOver' (N : ℕ) [NeZero N] (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    modularEval N (coeffSubring A K) p ∈ fieldOver N K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
      exact algebraMap_mem_fieldOver' K N ((mem_coeffSubring_iff' A K).mp c.2).2
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]; refine mul_mem hp ?_
      unfold modularEval; rw [MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact jqModC_mem_fieldOver' K N
      · exact jqNModC_mem_fieldOver'' K N

theorem isIntegral_jRing_jqNModC'' (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral ↥(jRing A K) (jqNModC (AlgebraicClosure ℚ) N) := by
  let jR : ↥(jRing A K) := ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_jRing'' A K⟩
  refine ⟨data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(jRing A K)) jR), data.monic.map _, ?_⟩
  let F := IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))
  have h0 : Polynomial.aeval (jqNModC (AlgebraicClosure ℚ) N) (minpoly ↥F (jqNModC (AlgebraicClosure ℚ) N)) = 0 :=
    minpoly.aeval ↥F _
  rw [ModularCurve.minpoly_jqNModC_eq (AlgebraicClosure ℚ) N data, Polynomial.aeval_def,
    Polynomial.eval₂_map] at h0
  rw [Polynomial.eval₂_map]
  convert h0 using 2 <;> try rfl
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [jR]
  rfl

theorem isIntegral_jRing_modularEval' (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    IsIntegral ↥(jRing A K) (modularEval N (coeffSubring A K) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
      exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, constSeries_mem_jRing' A K c⟩)
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
      rw [map_mul]; refine hp.mul ?_
      unfold modularEval; rw [MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, jqModC_mem_jRing'' A K⟩)
      · exact isIntegral_jRing_jqNModC'' A K N data

theorem modularEval_mem_jIntegralClosure {q : ℕ} [Fact q.Prime] (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) s ∈ jIntegralClosure (1 * q) A K := by
  have hq : q.Prime := Fact.out
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData_of_squarefree (1 * q)
    (by rw [one_mul]; exact hq.squarefree) (by rw [one_mul]; exact hq.one_lt)
  exact ⟨modularEval_mem_fieldOver' A K (1 * q) s, isIntegral_jRing_modularEval' A K (1 * q) data s⟩

theorem constSeries_mem_jIntegralClosure {q : ℕ} [Fact q.Prime] (b : ↥(coeffSubring A K)) :
    constSeries (coeffSubring A K) b ∈ jIntegralClosure (1 * q) A K := by
  have : constSeries (coeffSubring A K) b = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C b) := by
    unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
  rw [this]; exact modularEval_mem_jIntegralClosure A K _

theorem exists_pointEvalRange {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k) :
    ∃ ev : ↥((modularEval (1 * q) (coeffSubring A K)).range) →+* k,
      ∀ s : MvPolynomial (Fin 2) ↥(coeffSubring A K),
        ev ⟨modularEval (1 * q) (coeffSubring A K) s, s, rfl⟩
          = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s := by
  set mE := modularEval (1 * q) (coeffSubring A K) with hmE
  set pE := pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) with hpE
  have hker : ∀ s ∈ RingHom.ker mE, pE s = 0 := fun s hs =>
    pointEval_eq_zero_of_modularEval_eq_zero red a K s hs
  let ev₀ : (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ RingHom.ker mE) →+* k :=
    Ideal.Quotient.lift (RingHom.ker mE) pE hker
  refine ⟨ev₀.comp (RingHom.quotientKerEquivRange mE).symm.toRingHom, fun s => ?_⟩
  have h1 : (RingHom.quotientKerEquivRange mE).symm ⟨mE s, s, rfl⟩ = Ideal.Quotient.mk _ s := by
    apply (RingHom.quotientKerEquivRange mE).injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  change ev₀ ((RingHom.quotientKerEquivRange mE).symm ⟨mE s, s, rfl⟩) = pE s
  rw [h1]
  rfl

end Vocab
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

section CoeffRing

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem red_natCast_eq_zero (q : ℕ) {k : Type*} [Field k] [CharP k q] (red : A →+* k) :
    red (q : A) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem not_isUnit_natCast (q : ℕ) {k : Type*} [Field k] [CharP k q] (red : A →+* k) :
    ¬ IsUnit ((q : ℕ) : A) := by
  intro h
  have := h.map red
  rw [red_natCast_eq_zero q red] at this
  exact not_isUnit_zero this

variable (A) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

def coeffToA : ↥(coeffSubring A K) →+* A where
  toFun x := ⟨x, ((mem_coeffSubring_iff' A K).mp x.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coeffToA_apply_coe (x : ↥(coeffSubring A K)) : ((coeffToA A K x : A) : AlgebraicClosure ℚ) = x := rfl

theorem exists_pow_eq_mul_of_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (x y : R) (hx : ¬ IsUnit x) (hy0 : y ≠ 0) :
    ∃ (n : ℕ) (w : R), 0 < n ∧ x ^ n = w * y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨1, 0, one_pos, by rw [pow_one, zero_mul]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible hy0 hϖ

  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exfalso; apply hx; rw [pow_zero] at hu; exact IsUnit.of_mul_eq_one (u : R) hu
    · exact h
  refine ⟨n + 1, ϖ ^ (m * (n + 1) - n) * (v : R) * ((u⁻¹ : Rˣ) : R) ^ (n + 1), Nat.succ_pos n, ?_⟩
  have hx' : x = ϖ ^ m * ((u⁻¹ : Rˣ) : R) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  have hle : n ≤ m * (n + 1) := by nlinarith
  have hϖ' : ϖ ^ (m * (n + 1)) = ϖ ^ (m * (n + 1) - n) * (y * (v : R)) := by
    rw [hv, ← pow_add, Nat.sub_add_cancel hle]
  calc x ^ (n + 1) = (ϖ ^ m) ^ (n + 1) * ((u⁻¹ : Rˣ) : R) ^ (n + 1) := by rw [hx', mul_pow]
    _ = ϖ ^ (m * (n + 1) - n) * (y * (v : R)) * ((u⁻¹ : Rˣ) : R) ^ (n + 1) := by rw [← pow_mul, hϖ']
    _ = _ := by ring

theorem ker_red_eq_maximalIdeal (q : ℕ) [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k) :
    RingHom.ker red = IsLocalRing.maximalIdeal A := by
  apply le_antisymm
  · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red)
  intro x hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  rw [RingHom.mem_ker]

  let K' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {(x : AlgebraicClosure ℚ)}
  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
  haveI : FiniteDimensional ℚ K' :=
    IntermediateField.adjoin.finiteDimensional (halg.isAlgebraic (x : AlgebraicClosure ℚ)).isIntegral
  have hxK' : (x : AlgebraicClosure ℚ) ∈ K' := IntermediateField.mem_adjoin_simple_self ℚ _
  let x' : ↥(coeffSubring A K') := ⟨x, (mem_coeffSubring_iff' A K').mpr ⟨x.2, hxK'⟩⟩
  have hx'A : coeffToA A K' x' = x := Subtype.ext rfl
  have hq'A : coeffToA A K' (q : ↥(coeffSubring A K')) = (q : A) := map_natCast _ q
  have hx' : ¬ IsUnit x' := fun h => hx (hx'A ▸ h.map (coeffToA A K'))
  have hq' : ¬ IsUnit (q : ↥(coeffSubring A K')) := fun h =>
    not_isUnit_natCast q red (hq'A ▸ h.map (coeffToA A K'))
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K' with hK | hdvr
  ·
    rcases eq_or_ne (x : AlgebraicClosure ℚ) 0 with h0 | h0
    · have : x = 0 := Subtype.ext h0
      rw [this, map_zero]
    · exfalso; apply hx
      have hinv : (x : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K' := by
        rw [hK]; exact K'.inv_mem hxK'
      exact ⟨⟨x, ⟨_, ((mem_coeffSubring_iff' A K').mp hinv).1⟩,
        Subtype.ext (mul_inv_cancel₀ h0), Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩
  ·
    have hq0 : (q : ↥(coeffSubring A K')) ≠ 0 := by
      intro h
      have : ((q : ℕ) : AlgebraicClosure ℚ) = 0 := by
        have := congrArg (fun z : ↥(coeffSubring A K') => (z : AlgebraicClosure ℚ)) h
        simpa using this
      exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
    obtain ⟨n, w, hn, hxn⟩ := exists_pow_eq_mul_of_dvr x' (q : ↥(coeffSubring A K')) hx' hq0
    have hA : x ^ n = coeffToA A K' w * (q : A) := by
      rw [← hx'A, ← hq'A, ← map_pow, hxn, map_mul]
    have : red x ^ n = 0 := by rw [← map_pow, hA, map_mul, red_natCast_eq_zero q red, mul_zero]
    exact pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp hn) |>.mp this

theorem constSeries_notMem_of_natCast_notMem {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) [𝔭.IsPrime]
    (hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭)
    (b : ↥(coeffSubring A K)) (hb0 : (b : AlgebraicClosure ℚ) ≠ 0)
    (hb : constSeries (coeffSubring A K) b ∈ jIntegralClosure (1 * q) A K) :
    (⟨_, hb⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭 := by
  intro hb𝔭

  let cst : ↥(coeffSubring A K) →+* ↥(jIntegralClosure (1 * q) A K) :=
    { toFun := fun c => ⟨constSeries (coeffSubring A K) c, constSeries_mem_jIntegralClosure A K c⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  have hcstb : cst b = ⟨_, hb⟩ := Subtype.ext rfl
  have hcstq : cst (q : ↥(coeffSubring A K)) = ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) := map_natCast _ q

  have hunit : ¬ IsUnit b := by
    intro hu
    apply (inferInstance : 𝔭.IsPrime).ne_top
    rw [Ideal.eq_top_iff_one]
    have := hu.map cst
    rw [hcstb] at this
    obtain ⟨u, hu'⟩ := this
    have h1 : (1 : ↥(jIntegralClosure (1 * q) A K)) = ↑u⁻¹ * ⟨_, hb⟩ := by rw [← hu', Units.inv_mul]
    rw [h1]; exact Ideal.mul_mem_left _ _ hb𝔭
  have hmem : ∀ y : AlgebraicClosure ℚ, y ∈ coeffSubring A K ↔ y ∈ A ∧ y ∈ K := fun _ => Iff.rfl
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with hK | hdvr
  · apply hunit
    have e : ∀ y : AlgebraicClosure ℚ, y ∈ coeffSubring A K ↔ y ∈ K.toSubalgebra.toSubring := fun y => by rw [hK]
    have hbK : (b : AlgebraicClosure ℚ) ∈ K := (e _).mp b.2
    have hinv : (b : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := (e _).mpr (K.inv_mem hbK)
    exact ⟨⟨b, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hb0), Subtype.ext (inv_mul_cancel₀ hb0)⟩, rfl⟩
  · have hb0' : b ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
    have hqunit : ¬ IsUnit (q : ↥(coeffSubring A K)) := fun h =>
      not_isUnit_natCast q red ((map_natCast (coeffToA A K) q) ▸ h.map (coeffToA A K))
    obtain ⟨n, w, hn, hqn⟩ := exists_pow_eq_mul_of_dvr (q : ↥(coeffSubring A K)) b hqunit hb0'
    apply hq𝔭
    apply (inferInstance : 𝔭.IsPrime).mem_of_pow_mem n
    rw [← hcstq, ← map_pow, hqn, map_mul, hcstb]
    exact Ideal.mul_mem_left _ _ hb𝔭

end CoeffRing
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

section Domination

variable {A : ValuationSubring (AlgebraicClosure ℚ)} (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem exists_valuationSubring_dominating {C : Type*} [CommRing C]
    (𝔐 : Ideal C) (h𝔐 : 𝔐 ≠ ⊤) (σ₀ : C →+* AlgebraicClosure ℚ) (hker : RingHom.ker σ₀ ≤ 𝔐) :
    ∃ A'' : ValuationSubring (AlgebraicClosure ℚ), (∀ c : C, σ₀ c ∈ A'') ∧ ∀ c ∈ 𝔐, σ₀ c ∈ A''.nonunits := by
  let S : Subring (AlgebraicClosure ℚ) := σ₀.range
  let I : Ideal S := 𝔐.map σ₀.rangeRestrict
  have hI : I ≠ ⊤ := by
    intro htop
    rw [Ideal.eq_top_iff_one] at htop
    have hsurj : Function.Surjective σ₀.rangeRestrict := σ₀.rangeRestrict_surjective
    rw [Ideal.mem_map_iff_of_surjective _ hsurj] at htop
    obtain ⟨m, hm, hm1⟩ := htop
    apply h𝔐
    rw [Ideal.eq_top_iff_one]
    have : m - 1 ∈ RingHom.ker σ₀ := by
      rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      exact congrArg Subtype.val hm1
    have h1 : (1 : C) = m - (m - 1) := by ring
    rw [h1]
    exact 𝔐.sub_mem hm (hker this)
  obtain ⟨B, hSB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  refine ⟨B, fun c => hSB ⟨c, rfl⟩, fun c hc => hIB ⟨⟨σ₀ c, c, rfl⟩, Ideal.mem_map_of_mem _ hc, rfl⟩⟩

theorem mem_nonunits_iff_of_forall_mem_iff (A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ))
    (τ : AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ)
    (hτ : ∀ x : AlgebraicClosure ℚ, x ∈ A₁ ↔ τ x ∈ A₂) (x : AlgebraicClosure ℚ) :
    x ∈ A₁.nonunits ↔ τ x ∈ A₂.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    map_eq_zero_iff τ τ.injective, ← map_inv₀, ← hτ]

end Domination
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

section Theta

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem isDiscreteValuationRing_coeffSubring (q : ℕ) [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) [FiniteDimensional ℚ K] : IsDiscreteValuationRing ↥(coeffSubring A K) := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with hK | h
  · exfalso
    apply not_isUnit_natCast q red
    have e : ∀ y : AlgebraicClosure ℚ, y ∈ coeffSubring A K ↔ y ∈ K.toSubalgebra.toSubring := fun y => by rw [hK]
    have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    have hinv : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K :=
      (e _).mpr (K.inv_mem (IntermediateField.natCast_mem K q))
    refine ⟨⟨(q : A), ⟨_, ((mem_coeffSubring_iff' A K).mp hinv).1⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · simp [mul_inv_cancel₀ hq0]
    · simp [inv_mul_cancel₀ hq0]
  · exact h

theorem redRestrict_apply {k : Type*} [Field k] (red : A →+* k) (b : ↥(coeffSubring A K)) :
    redRestrict red K b = red (coeffToA A K b) := rfl

theorem isUnit_of_redRestrict_ne_zero (q : ℕ) [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    {b : ↥(coeffSubring A K)} (hb : redRestrict red K b ≠ 0) : IsUnit b := by
  have hbA : IsUnit (coeffToA A K b) := by
    by_contra h
    apply hb
    rw [redRestrict_apply, ← RingHom.mem_ker, ker_red_eq_maximalIdeal A q red]
    exact h

  obtain ⟨u, hu⟩ := hbA
  have hb0 : (b : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hb
    have : b = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hinvA : (b : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have : ((u⁻¹ : Aˣ) : A) = ((b : AlgebraicClosure ℚ)⁻¹ : AlgebraicClosure ℚ) := by
      have h1 : ((u : A) : AlgebraicClosure ℚ) * ((u⁻¹ : Aˣ) : A) = 1 := by
        rw [← Subring.coe_mul] ; exact congrArg Subtype.val u.mul_inv
      rw [hu] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    rw [← this]; exact ((u⁻¹ : Aˣ) : A).2
  have hinv : (b : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K :=
    (mem_coeffSubring_iff' A K).mpr ⟨hinvA, K.inv_mem ((mem_coeffSubring_iff' A K).mp b.2).2⟩
  exact ⟨⟨b, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hb0), Subtype.ext (inv_mul_cancel₀ hb0)⟩, rfl⟩

def jEvalC (q : ℕ) [Fact q.Prime] : Polynomial ↥(coeffSubring A K) →+* ↥(jIntegralClosure (1 * q) A K) :=
  ((modularEval (1 * q) (coeffSubring A K)).codRestrict (jIntegralClosure (1 * q) A K)
      (modularEval_mem_jIntegralClosure A K)).comp
    (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))

theorem coe_jEvalC (q : ℕ) [Fact q.Prime] (p : Polynomial ↥(coeffSubring A K)) :
    (jEvalC A K q p : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) (coeffSubring A K) (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) p) := rfl

theorem coe_jEvalC_eq_aeval (q : ℕ) [Fact q.Prime] (p : Polynomial ↥(coeffSubring A K)) :
    (jEvalC A K q p : LaurentSeries (AlgebraicClosure ℚ))
      = Polynomial.aeval (jqModC (AlgebraicClosure ℚ)) (p.map (Subring.subtype (coeffSubring A K))) := by
  rw [coe_jEvalC, Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  · ext c; unfold modularEval; rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]; rfl
  · unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl

theorem coe_jEvalC_eq_jEval (q : ℕ) [Fact q.Prime] (p : Polynomial ↥(coeffSubring A K)) :
    (jEvalC A K q p : LaurentSeries (AlgebraicClosure ℚ)) = jEval A K p := by
  rw [coe_jEvalC_eq_aeval, jEval_eq_aeval_map]

theorem jEvalC_injective (q : ℕ) [Fact q.Prime] : Function.Injective (jEvalC A K q) := by
  intro p₁ p₂ h
  have h' := congrArg (fun z : ↥(jIntegralClosure (1 * q) A K) => (z : LaurentSeries (AlgebraicClosure ℚ))) h
  simp only [coe_jEvalC_eq_aeval A K q] at h'
  have hinj := (transcendental_iff_injective.mp (ModularCurve.transcendental_jqModC (AlgebraicClosure ℚ)))
  exact Polynomial.map_injective _ Subtype.val_injective (hinj h')

theorem exists_polynomial_mem_and_map_ne_zero {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭) :
    ∃ p : Polynomial ↥(coeffSubring A K), jEvalC A K q p ∈ 𝔭 ∧ p.map (redRestrict red K) ≠ 0 := by
  haveI := isDiscreteValuationRing_coeffSubring A K q red

  have h𝔭0 : 𝔭 ≠ ⊥ := by
    rintro rfl; rw [Ideal.height_bot] at h𝔭; exact zero_ne_one h𝔭
  have hcomap : 𝔭.comap (jEvalC A K q) ≠ ⊥ := by
    obtain ⟨x, hx𝔭, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭0
    letI : Algebra (Polynomial ↥(coeffSubring A K)) ↥(jIntegralClosure (1 * q) A K) := (jEvalC A K q).toAlgebra
    refine Ideal.comap_ne_bot_of_integral_mem hx0 hx𝔭 ?_

    obtain ⟨P, hPm, hPx⟩ := x.2.2
    let e := polynomialEquivJRing A K
    refine ⟨P.map e.symm.toRingHom, hPm.map _, ?_⟩
    apply Subtype.val_injective
    change ((Polynomial.eval₂ (jEvalC A K q) x (P.map e.symm.toRingHom) : ↥(jIntegralClosure (1 * q) A K))
      : LaurentSeries (AlgebraicClosure ℚ)) = 0
    rw [Polynomial.eval₂_map,
      show ((Polynomial.eval₂ ((jEvalC A K q).comp e.symm.toRingHom) x P : ↥(jIntegralClosure (1 * q) A K))
        : LaurentSeries (AlgebraicClosure ℚ))
        = (jIntegralClosure (1 * q) A K).subtype (Polynomial.eval₂ ((jEvalC A K q).comp e.symm.toRingHom) x P)
        from rfl,
      Polynomial.hom_eval₂]
    have hcomp : (jIntegralClosure (1 * q) A K).subtype.comp ((jEvalC A K q).comp e.symm.toRingHom)
        = algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) := by
      refine RingHom.ext fun c => ?_
      change ((jEvalC A K q (e.symm c) : ↥(jIntegralClosure (1 * q) A K)) : LaurentSeries (AlgebraicClosure ℚ)) = c
      rw [coe_jEvalC_eq_jEval]
      have : (c : LaurentSeries (AlgebraicClosure ℚ)) = (e (e.symm c) : LaurentSeries (AlgebraicClosure ℚ)) := by
        rw [RingEquiv.apply_symm_apply]
      rw [this, coe_polynomialEquivJRing]
      rfl
    rw [hcomp]
    exact hPx
  obtain ⟨p, hp𝔭, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
  rw [Ideal.mem_comap] at hp𝔭

  letI : NormalizationMonoid ↥(coeffSubring A K) :=
    (UniqueFactorizationMonoid.normalizationMonoid : StrongNormalizationMonoid ↥(coeffSubring A K)).toNormalizationMonoid
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid ↥(coeffSubring A K)
  have hpc : p = Polynomial.C p.content * p.primPart := p.eq_C_content_mul_primPart
  have hc0 : p.content ≠ 0 := fun h => hp0 (Polynomial.content_eq_zero_iff.mp h)
  refine ⟨p.primPart, ?_, ?_⟩
  ·
    have hmul : jEvalC A K q (Polynomial.C p.content) * jEvalC A K q p.primPart ∈ 𝔭 := by
      rw [← map_mul, ← hpc]; exact hp𝔭
    rcases (inferInstance : 𝔭.IsPrime).mem_or_mem hmul with h | h
    · exfalso
      have hc0' : ((p.content : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := fun e => hc0 (Subtype.ext e)
      apply constSeries_notMem_of_natCast_notMem A K red 𝔭 hq𝔭 p.content hc0' (constSeries_mem_jIntegralClosure A K _)
      convert h using 1
      apply Subtype.ext
      rw [coe_jEvalC, Polynomial.eval₂_C]; unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
    · exact h
  · intro h0
    have hprim := p.isPrimitive_primPart
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
    apply hϖ.not_isUnit
    apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprim ϖ
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hi : redRestrict red K (p.primPart.coeff i) = 0 := by
      have := congrArg (fun r => Polynomial.coeff r i) h0
      simpa [Polynomial.coeff_map] using this

    have hnu : ¬ IsUnit (p.primPart.coeff i) := by
      intro hu
      have := hu.map (redRestrict red K)
      rw [hi] at this
      exact not_isUnit_zero this
    have hmem : p.primPart.coeff i ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := hnu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton] at hmem
    exact hmem

end Theta
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

section ThetaMain

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

def residueSubfield (q : ℕ) [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k) : Subfield k where
  carrier := Set.range (redRestrict red K)
  mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩
  one_mem' := ⟨1, map_one _⟩
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  neg_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨-x, map_neg _ _⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    by_cases hx : redRestrict red K x = 0
    · rw [hx, inv_zero]; exact ⟨0, map_zero _⟩
    · obtain ⟨u, rfl⟩ := isUnit_of_redRestrict_ne_zero A K q red hx
      refine ⟨((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)), eq_inv_of_mul_eq_one_left ?_⟩
      rw [← map_mul, Units.inv_mul, map_one]

theorem mem_residueSubfield_iff (q : ℕ) [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k) {y : k} :
    y ∈ residueSubfield A K q red ↔ ∃ x, redRestrict red K x = y := Iff.rfl

theorem exists_maximal_ringHom_algClosure {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (a : k) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭)
    (h𝔭S : ∀ s : MvPolynomial (Fin 2) ↥(coeffSubring A K), pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0 →
      ∀ hs : modularEval (1 * q) (coeffSubring A K) s ∈ jIntegralClosure (1 * q) A K,
        (⟨_, hs⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭) :
    ∃ (𝔐 : Ideal ↥(jIntegralClosure (1 * q) A K)) (_ : 𝔐.IsMaximal) (θ : ↥(jIntegralClosure (1 * q) A K) →+* AlgebraicClosure k),
      𝔭 ≤ 𝔐 ∧ RingHom.ker θ = 𝔐 ∧
      ∀ s : MvPolynomial (Fin 2) ↥(coeffSubring A K),
        θ ⟨_, modularEval_mem_jIntegralClosure A K s⟩
          = algebraMap k (AlgebraicClosure k) (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s) := by
  classical
  let B : Subring (LaurentSeries (AlgebraicClosure ℚ)) := (modularEval (1 * q) (coeffSubring A K)).range
  have hBC : B ≤ (jIntegralClosure (1 * q) A K) := by rintro _ ⟨s, rfl⟩; exact modularEval_mem_jIntegralClosure A K s
  letI : Algebra B ↥(jIntegralClosure (1 * q) A K) := (Subring.inclusion hBC).toAlgebra

  have hJB : jRing A K ≤ B := by
    rw [jRing, Subring.closure_le]
    rintro x (⟨c, rfl⟩ | rfl)
    · exact ⟨MvPolynomial.C c, by unfold modularEval; rw [MvPolynomial.eval₂Hom_C]⟩
    · exact ⟨MvPolynomial.X 0, by unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl⟩
  haveI : Algebra.IsIntegral B ↥(jIntegralClosure (1 * q) A K) := ⟨fun x => by
    obtain ⟨P, hPm, hPx⟩ := x.2.2
    refine ⟨P.map (Subring.inclusion hJB), hPm.map _, ?_⟩
    apply Subtype.val_injective
    change ((Polynomial.eval₂ (algebraMap B ↥(jIntegralClosure (1 * q) A K)) x (P.map (Subring.inclusion hJB)) : ↥(jIntegralClosure (1 * q) A K))
      : LaurentSeries (AlgebraicClosure ℚ)) = 0
    rw [Polynomial.eval₂_map,
      show ((Polynomial.eval₂ ((algebraMap B ↥(jIntegralClosure (1 * q) A K)).comp (Subring.inclusion hJB)) x P : ↥(jIntegralClosure (1 * q) A K))
          : LaurentSeries (AlgebraicClosure ℚ))
        = (jIntegralClosure (1 * q) A K).subtype (Polynomial.eval₂ ((algebraMap B ↥(jIntegralClosure (1 * q) A K)).comp (Subring.inclusion hJB)) x P) from rfl,
      Polynomial.hom_eval₂]
    have : (jIntegralClosure (1 * q) A K).subtype.comp ((algebraMap B ↥(jIntegralClosure (1 * q) A K)).comp (Subring.inclusion hJB))
        = algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) := RingHom.ext fun _ => rfl
    rw [this]; exact hPx⟩

  obtain ⟨ev, hev⟩ := exists_pointEvalRange A K red a (q := q)
  let 𝔫 : Ideal B := RingHom.ker ev
  haveI h𝔫prime : 𝔫.IsPrime := RingHom.ker_isPrime ev

  have h𝔭𝔫 : 𝔭.comap (algebraMap B ↥(jIntegralClosure (1 * q) A K)) ≤ 𝔫 := by
    intro x hx
    obtain ⟨s, hs⟩ := x.2
    have hxs : x = ⟨(modularEval (1 * q) (coeffSubring A K)) s, s, rfl⟩ := Subtype.ext hs.symm
    rw [RingHom.mem_ker, hxs, hev]
    by_contra hne
    apply h𝔭S s hne (modularEval_mem_jIntegralClosure A K s)
    rw [Ideal.mem_comap, hxs] at hx
    exact hx

  obtain ⟨Q, hQ𝔭, hQprime, hQcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔫 𝔭 h𝔭𝔫
  haveI := hQprime
  haveI hQlies : Q.LiesOver 𝔫 := ⟨hQcomap.symm⟩

  let k₀ := residueSubfield A K q red
  have hrange_le : ∀ s, (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)) s ∈ (Algebra.adjoin ↥k₀ ({a} : Set k)).toSubring := by
    intro s
    change MvPolynomial.eval₂ (redRestrict red K) ![a, a ^ q] s ∈ (Algebra.adjoin ↥k₀ ({a} : Set k)).toSubring
    induction s using MvPolynomial.induction_on with
    | C c =>
        rw [MvPolynomial.eval₂_C]
        exact (Algebra.adjoin ↥k₀ ({a} : Set k)).algebraMap_mem (⟨redRestrict red K c, c, rfl⟩ : ↥k₀)
    | add p q hp hq => rw [MvPolynomial.eval₂_add]; exact add_mem hp hq
    | mul_X p i hp =>
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
        refine mul_mem hp ?_
        fin_cases i
        · exact Algebra.subset_adjoin (Set.mem_singleton a)
        · change a ^ q ∈ (Algebra.adjoin ↥k₀ ({a} : Set k)).toSubring
          exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton a)) q
  have hrange_ge : (Algebra.adjoin ↥k₀ ({a} : Set k)).toSubring ≤ ev.range := by
    let S : Subalgebra ↥k₀ k :=
      { toSubsemiring := ev.range.toSubsemiring
        algebraMap_mem' := fun c => by
          obtain ⟨b, hb⟩ := c.2
          refine ⟨⟨(modularEval (1 * q) (coeffSubring A K)) (MvPolynomial.C b), MvPolynomial.C b, rfl⟩, ?_⟩
          rw [hev]; unfold pointEval; rw [MvPolynomial.eval₂Hom_C]; exact hb }
    have ha : a ∈ S := ⟨⟨(modularEval (1 * q) (coeffSubring A K)) (MvPolynomial.X 0), MvPolynomial.X 0, rfl⟩, by
      rw [hev]; unfold pointEval; rw [MvPolynomial.eval₂Hom_X']; rfl⟩
    have : Algebra.adjoin ↥k₀ ({a} : Set k) ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr ha)
    exact fun x hx => this hx
  have hrangeEq : ev.range = (Algebra.adjoin ↥k₀ ({a} : Set k)).toSubring := by
    refine le_antisymm ?_ hrange_ge
    rintro _ ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := x.2
    have hxs : x = ⟨(modularEval (1 * q) (coeffSubring A K)) s, s, rfl⟩ := Subtype.ext hs.symm
    rw [hxs, hev]; exact hrange_le s

  obtain ⟨p, hp𝔭, hp0⟩ := exists_polynomial_mem_and_map_ne_zero A K red 𝔭 h𝔭 hq𝔭
  let red₀' : ↥(coeffSubring A K) →+* ↥k₀ :=
    { toFun := fun b => ⟨redRestrict red K b, b, rfl⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  have hred₀' : (algebraMap ↥k₀ k).comp red₀' = redRestrict red K := RingHom.ext fun _ => rfl
  have halg : IsAlgebraic ↥k₀ a := by
    refine ⟨p.map red₀', ?_, ?_⟩
    · intro h0
      apply hp0
      have := congrArg (Polynomial.map (algebraMap ↥k₀ k)) h0
      rwa [Polynomial.map_map, hred₀', Polynomial.map_zero] at this
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map, hred₀']

      have h1 : (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)) (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) p)
          = Polynomial.eval₂ (redRestrict red K) a p := by
        rw [Polynomial.hom_eval₂]
        congr 1
        · ext b; unfold pointEval; rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        · unfold pointEval; rw [MvPolynomial.eval₂Hom_X']; rfl
      rw [← h1, ← hev]
      have hmem : (⟨(modularEval (1 * q) (coeffSubring A K)) (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) p), _, rfl⟩ : ↥(modularEval (1 * q) (coeffSubring A K)).range) ∈ 𝔫 := by
        apply h𝔭𝔫
        rw [Ideal.mem_comap]
        convert hp𝔭 using 1 <;> try rfl
      exact hmem
  have hadj : ev.range = (IntermediateField.adjoin ↥k₀ ({a} : Set k)).toSubalgebra.toSubring := by
    rw [hrangeEq, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
  have hmemiff : ∀ y : k, y ∈ ev.range ↔ y ∈ IntermediateField.adjoin ↥k₀ ({a} : Set k) := fun y => by
    rw [hadj]; exact Iff.rfl
  have hfieldRange : IsField ↥(ev.range) := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx => ?_⟩
    have hx0 : (x : k) ≠ 0 := fun h => hx (Subtype.ext h)
    have hxK : (x : k) ∈ IntermediateField.adjoin ↥k₀ ({a} : Set k) := (hmemiff _).mp x.2
    have hinv : (x : k)⁻¹ ∈ ev.range :=
      (hmemiff _).mpr ((IntermediateField.adjoin ↥k₀ ({a} : Set k)).inv_mem hxK)
    exact ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
  have h𝔫max : 𝔫.IsMaximal :=
    Ideal.Quotient.maximal_of_isField 𝔫 (MulEquiv.isField hfieldRange (RingHom.quotientKerEquivRange ev).toMulEquiv)
  have hQmax : Q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ↥B) Q (hQcomap.symm ▸ h𝔫max)

  letI : Field (↥B ⧸ 𝔫) := Ideal.Quotient.field 𝔫
  letI : Field (↥(jIntegralClosure (1 * q) A K) ⧸ Q) := Ideal.Quotient.field Q
  let evbar : ↥B ⧸ 𝔫 →+* k := Ideal.Quotient.lift 𝔫 ev (fun _ h => h)
  letI : Algebra (↥B ⧸ 𝔫) (AlgebraicClosure k) := ((algebraMap k (AlgebraicClosure k)).comp evbar).toAlgebra
  haveI : FaithfulSMul (↥B ⧸ 𝔫) (AlgebraicClosure k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr ((algebraMap k (AlgebraicClosure k)).injective.comp evbar.injective)
  haveI : FaithfulSMul (↥B ⧸ 𝔫) (↥(jIntegralClosure (1 * q) A K) ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (↥B ⧸ 𝔫) (↥(jIntegralClosure (1 * q) A K) ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (↥B ⧸ 𝔫) (AlgebraicClosure k) := inferInstance
  haveI : Algebra.IsAlgebraic (↥B ⧸ 𝔫) (↥(jIntegralClosure (1 * q) A K) ⧸ Q) := inferInstance
  let θ₀ : (↥(jIntegralClosure (1 * q) A K) ⧸ Q) →ₐ[↥B ⧸ 𝔫] AlgebraicClosure k := IsAlgClosed.lift
  refine ⟨Q, hQmax, θ₀.toRingHom.comp (Ideal.Quotient.mk Q), hQ𝔭, ?_, ?_⟩
  · ext c
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ θ₀.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]
  · intro s
    have h1 : (⟨_, modularEval_mem_jIntegralClosure A K s⟩ : ↥(jIntegralClosure (1 * q) A K)) = algebraMap ↥B ↥(jIntegralClosure (1 * q) A K) ⟨(modularEval (1 * q) (coeffSubring A K)) s, s, rfl⟩ :=
      Subtype.ext rfl
    rw [h1, RingHom.comp_apply,
      show Ideal.Quotient.mk Q (algebraMap ↥B ↥(jIntegralClosure (1 * q) A K) ⟨(modularEval (1 * q) (coeffSubring A K)) s, s, rfl⟩)
        = algebraMap (↥B ⧸ 𝔫) (↥(jIntegralClosure (1 * q) A K) ⧸ Q) (Ideal.Quotient.mk 𝔫 ⟨(modularEval (1 * q) (coeffSubring A K)) s, s, rfl⟩) from rfl]
    change θ₀ _ = _
    rw [AlgHom.commutes]
    change algebraMap k (AlgebraicClosure k) (evbar (Ideal.Quotient.mk 𝔫 _)) = _
    rw [Ideal.Quotient.lift_mk, hev]

end ThetaMain
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

section SigmaZero

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

def cstC (q : ℕ) [Fact q.Prime] : ↥(coeffSubring A K) →+* ↥(jIntegralClosure (1 * q) A K) where
  toFun c := ⟨constSeries (coeffSubring A K) c, constSeries_mem_jIntegralClosure A K c⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

theorem coe_cstC (q : ℕ) [Fact q.Prime] (c : ↥(coeffSubring A K)) :
    ((cstC A K q c : ↥(jIntegralClosure (1 * q) A K)) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) := rfl

theorem exists_ringHom_ker_eq {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭) :
    ∃ σ₀ : ↥(jIntegralClosure (1 * q) A K) →+* AlgebraicClosure ℚ, RingHom.ker σ₀ = 𝔭 ∧
      ∀ (b : ↥(coeffSubring A K)) (hb : constSeries (coeffSubring A K) b ∈ jIntegralClosure (1 * q) A K),
        σ₀ ⟨_, hb⟩ = b := by
  classical
  letI : Algebra ↥(coeffSubring A K) ↥(jIntegralClosure (1 * q) A K) := (cstC A K q).toAlgebra

  haveI : FaithfulSMul ↥(coeffSubring A K) (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔭) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro b₁ b₂ h
    by_contra hne
    have hsub : (b₁ - b₂ : ↥(coeffSubring A K)) ≠ 0 := sub_ne_zero.mpr hne
    have hsub' : ((b₁ - b₂ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := fun e => hsub (Subtype.ext e)
    apply constSeries_notMem_of_natCast_notMem A K red 𝔭 hq𝔭 (b₁ - b₂) hsub' (constSeries_mem_jIntegralClosure A K _)
    have : algebraMap ↥(coeffSubring A K) (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔭) (b₁ - b₂) = 0 := by
      rw [map_sub, h, sub_self]
    rw [IsScalarTower.algebraMap_apply ↥(coeffSubring A K) ↥(jIntegralClosure (1 * q) A K) (_ ⧸ 𝔭),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this

  haveI : Algebra.IsAlgebraic ↥(coeffSubring A K) (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔭) := by
    let jC : ↥(jIntegralClosure (1 * q) A K) := ⟨_, modularEval_mem_jIntegralClosure A K (MvPolynomial.X 0)⟩
    have hjC : (jC : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
      change modularEval _ _ _ = _; unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl
    have haevalC : ∀ p' : Polynomial ↥(coeffSubring A K), Polynomial.aeval jC p' = jEvalC A K q p' := by
      intro p'
      apply Subtype.ext
      rw [coe_jEvalC_eq_jEval, jEval_apply, Polynomial.aeval_def,
        show ((Polynomial.eval₂ (algebraMap ↥(coeffSubring A K) ↥(jIntegralClosure (1 * q) A K)) jC p'
            : ↥(jIntegralClosure (1 * q) A K)) : LaurentSeries (AlgebraicClosure ℚ))
          = (jIntegralClosure (1 * q) A K).subtype (Polynomial.eval₂ (algebraMap _ _) jC p') from rfl,
        Polynomial.hom_eval₂]
      have hf : (jIntegralClosure (1 * q) A K).subtype.comp
          (algebraMap ↥(coeffSubring A K) ↥(jIntegralClosure (1 * q) A K)) = constSeries (coeffSubring A K) :=
        RingHom.ext fun _ => rfl
      rw [hf]
      exact congrArg (fun z => Polynomial.eval₂ (constSeries (coeffSubring A K)) z p') hjC
    obtain ⟨p, hp𝔭, hp0⟩ := exists_polynomial_mem_and_map_ne_zero A K red 𝔭 h𝔭 hq𝔭
    have hpne : p ≠ 0 := by rintro rfl; exact hp0 (Polynomial.map_zero _)
    let jbar : ↥(jIntegralClosure (1 * q) A K) ⧸ 𝔭 := Ideal.Quotient.mk 𝔭 jC
    have halgj : IsAlgebraic ↥(coeffSubring A K) jbar := by
      refine ⟨p, hpne, ?_⟩
      change Polynomial.aeval (Ideal.Quotient.mkₐ ↥(coeffSubring A K) 𝔭 jC) p = 0
      rw [Polynomial.aeval_algHom_apply, haevalC, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hp𝔭

    let D : Subalgebra ↥(coeffSubring A K) (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔭) :=
      Algebra.adjoin ↥(coeffSubring A K) {jbar}
    haveI : Algebra.IsAlgebraic ↥(coeffSubring A K) ↥D :=
      (Subalgebra.isAlgebraic_iff _).mp (Algebra.isAlgebraic_adjoin_singleton_iff.mpr halgj)
    let e := polynomialEquivJRing A K
    let φ₀ : ↥(jRing A K) →+* (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔭) :=
      (Polynomial.aeval jbar).toRingHom.comp e.symm.toRingHom
    have hφ₀D : ∀ y, φ₀ y ∈ D := fun y => Polynomial.aeval_mem_adjoin_singleton _ _
    have hJC : ∀ y : ↥(jRing A K), (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (1 * q) A K :=
      fun y => by
        have : (y : LaurentSeries (AlgebraicClosure ℚ)) = jEval A K (e.symm y) := by
          change _ = ((e (e.symm y) : ↥(jRing A K)) : LaurentSeries (AlgebraicClosure ℚ))
          rw [e.apply_symm_apply]
        rw [this, ← coe_jEvalC_eq_jEval A K q]; exact (jEvalC A K q (e.symm y)).2
    have hφ₀ : ∀ y : ↥(jRing A K), φ₀ y = Ideal.Quotient.mk 𝔭 ⟨y, hJC y⟩ := by
      intro y
      change Polynomial.aeval (Ideal.Quotient.mkₐ ↥(coeffSubring A K) 𝔭 jC) (e.symm y) = _
      rw [Polynomial.aeval_algHom_apply, haevalC, Ideal.Quotient.mkₐ_eq_mk]
      congr 1
      apply Subtype.ext
      rw [coe_jEvalC_eq_jEval]
      change ((e (e.symm y) : ↥(jRing A K)) : LaurentSeries (AlgebraicClosure ℚ)) = (y : LaurentSeries (AlgebraicClosure ℚ))
      rw [e.apply_symm_apply]
    let φ : ↥(jRing A K) →+* ↥D := φ₀.codRestrict D.toSubring hφ₀D
    refine Algebra.IsAlgebraic.mk fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨P, hPm, hPx⟩ := x.2.2
    have hintD : IsIntegral ↥D (Ideal.Quotient.mk 𝔭 x) := by
      refine ⟨P.map φ, hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      let ι : ↥(jRing A K) →+* ↥(jIntegralClosure (1 * q) A K) :=
        { toFun := fun y => ⟨y, hJC y⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hcomp : (algebraMap ↥D (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔭)).comp φ
          = (Ideal.Quotient.mk 𝔭).comp ι := RingHom.ext fun y => hφ₀ y
      rw [hcomp, ← Polynomial.hom_eval₂]
      have h0 : Polynomial.eval₂ ι x P = 0 := by
        apply Subtype.ext
        rw [show ((Polynomial.eval₂ ι x P : ↥(jIntegralClosure (1 * q) A K)) : LaurentSeries (AlgebraicClosure ℚ))
            = (jIntegralClosure (1 * q) A K).subtype (Polynomial.eval₂ ι x P) from rfl, Polynomial.hom_eval₂]
        exact hPx
      rw [h0, map_zero]
    exact IsIntegral.trans_isAlgebraic (R := ↥(coeffSubring A K)) hintD

  let σbar : (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔭) →ₐ[↥(coeffSubring A K)] AlgebraicClosure ℚ := IsAlgClosed.lift
  have hinj : Function.Injective σbar := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    have halg : IsAlgebraic ↥(coeffSubring A K) y := Algebra.IsAlgebraic.isAlgebraic y
    have hne := Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker σbar.toRingHom) hy0 hy halg
    apply hne
    rw [eq_bot_iff]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker] at hb
    change σbar (algebraMap _ _ b) = 0 at hb
    rw [AlgHom.commutes] at hb
    have : (b : AlgebraicClosure ℚ) = 0 := hb
    exact (Submodule.mem_bot _).mpr (Subtype.ext this)
  refine ⟨σbar.toRingHom.comp (Ideal.Quotient.mk 𝔭), ?_, ?_⟩
  · ext c
    rw [RingHom.mem_ker, RingHom.comp_apply]
    change σbar (Ideal.Quotient.mk 𝔭 c) = 0 ↔ _
    rw [map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
  · intro b hb
    have h1 : (⟨_, hb⟩ : ↥(jIntegralClosure (1 * q) A K)) = algebraMap ↥(coeffSubring A K) _ b := Subtype.ext rfl
    rw [h1, RingHom.comp_apply, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    change σbar (algebraMap _ _ b) = _
    rw [AlgHom.commutes]
    rfl

end SigmaZero
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

end NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

section Finiteness

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

set_option maxHeartbeats 12800000 in
theorem module_finite_jIntegralClosure {q : ℕ} [Fact q.Prime] [FiniteDimensional ℚ K] :
    Module.Finite ↥(jRing A K) ↥(jIntegralClosure (1 * q) A K) := by
  classical
  have hq : q.Prime := Fact.out
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData_of_squarefree (1 * q)
    (by rw [one_mul]; exact hq.squarefree) (by rw [one_mul]; exact hq.one_lt)
  obtain ⟨hN, hIC, hD⟩ := blockB A K
  haveI : IsNoetherianRing ↥(jRing A K) := isNoetherianRing_of_ringEquiv _ (polynomialEquivJRing A K)
  haveI : IsIntegrallyClosed ↥(jRing A K) := IsIntegrallyClosed.of_equiv (polynomialEquivJRing A K)
  letI : Algebra (FractionRing ↥(jRing A K)) ↥(fieldOver (1 * q) K) :=
    FractionRing.liftAlgebra ↥(jRing A K) ↥(fieldOver (1 * q) K)
  have hint : IsIntegral (FractionRing ↥(jRing A K)) (jN K (1 * q)) :=
    (isIntegral_jRing_jN A K (1 * q) data).tower_top
  haveI hfd : FiniteDimensional (FractionRing ↥(jRing A K)) ↥(fieldOver (1 * q) K) := by
    have h1 : FiniteDimensional (FractionRing ↥(jRing A K))
        ↥(IntermediateField.adjoin (FractionRing ↥(jRing A K)) ({jN K (1 * q)} : Set ↥(fieldOver (1 * q) K))) :=
      IntermediateField.adjoin.finiteDimensional hint
    rw [adjoin_jN_eq_top A K (1 * q) (FractionRing ↥(jRing A K))] at h1
    exact LinearEquiv.finiteDimensional
      (IntermediateField.topEquiv (F := FractionRing ↥(jRing A K)) (E := ↥(fieldOver (1 * q) K))).toLinearEquiv
  haveI : CharZero (FractionRing ↥(jRing A K)) :=
    (algebraMap (FractionRing ↥(jRing A K)) ↥(fieldOver (1 * q) K)).charZero
  exact IsIntegralClosure.finite ↥(jRing A K) (FractionRing ↥(jRing A K)) ↥(fieldOver (1 * q) K) _

theorem finiteDimensional_adjoin_range {q : ℕ} [Fact q.Prime] [FiniteDimensional ℚ K]
    (σ : ↥(jIntegralClosure (1 * q) A K) →+* AlgebraicClosure ℚ)
    (hσK : ∀ (b : ↥(coeffSubring A K)) (hb : CharPReduction.constSeries (coeffSubring A K) b ∈ jIntegralClosure (1 * q) A K),
      σ ⟨_, hb⟩ = b) :
    FiniteDimensional ↥K (IntermediateField.adjoin ↥K (Set.range σ)) := by
  classical
  haveI := module_finite_jIntegralClosure A K (q := q)
  obtain ⟨T, hT⟩ := Module.finite_def.mp (inferInstance : Module.Finite ↥(jRing A K) ↥(jIntegralClosure (1 * q) A K))

  let jC : ↥(jIntegralClosure (1 * q) A K) := ⟨_, modularEval_mem_jIntegralClosure A K (MvPolynomial.X 0)⟩
  have hjC : (jC : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    change modularEval _ _ _ = _; unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl
  let S : Finset (AlgebraicClosure ℚ) := insert (σ jC) (T.image σ)
  have halg0 : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
  haveI : FiniteDimensional ↥K (IntermediateField.adjoin ↥K (S : Set (AlgebraicClosure ℚ))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => ((halg0.isAlgebraic x).tower_top (L := ↥K)).isIntegral
  suffices hle : IntermediateField.adjoin ↥K (Set.range σ) ≤ IntermediateField.adjoin ↥K (S : Set (AlgebraicClosure ℚ)) by
    exact Submodule.finiteDimensional_of_le (S₁ := (IntermediateField.adjoin ↥K (Set.range σ)).toSubalgebra.toSubmodule)
      (S₂ := (IntermediateField.adjoin ↥K (S : Set (AlgebraicClosure ℚ))).toSubalgebra.toSubmodule) hle
  rw [IntermediateField.adjoin_le_iff]

  set E := IntermediateField.adjoin ↥K (S : Set (AlgebraicClosure ℚ)) with hE
  have hjE : σ jC ∈ E := IntermediateField.subset_adjoin _ _ (Finset.mem_insert_self _ _)

  have hJ : ∀ (y : LaurentSeries (AlgebraicClosure ℚ)) (hy : y ∈ jRing A K) (hyC : y ∈ jIntegralClosure (1 * q) A K),
      σ ⟨y, hyC⟩ ∈ E := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
        intro hzC
        rcases hz with ⟨c, rfl⟩ | rfl
        · rw [hσK]; exact E.algebraMap_mem ⟨(c : AlgebraicClosure ℚ), ((Subring.mem_inf).mp c.2).2⟩
        · have : (⟨_, hzC⟩ : ↥(jIntegralClosure (1 * q) A K)) = jC := Subtype.ext hjC.symm
          rw [this]; exact hjE
    | one => intro h; have : (⟨_, h⟩ : ↥(jIntegralClosure (1 * q) A K)) = 1 := rfl
             rw [this, map_one]; exact one_mem E
    | zero => intro h; have : (⟨_, h⟩ : ↥(jIntegralClosure (1 * q) A K)) = 0 := rfl
              rw [this, map_zero]; exact zero_mem E
    | add y z hy' hz' ihy ihz =>
        intro h
        have hyC : y ∈ jIntegralClosure (1 * q) A K := ⟨jRing_le_fieldOver' A K (1 * q) hy', isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨y, hy'⟩)⟩
        have hzC : z ∈ jIntegralClosure (1 * q) A K := ⟨jRing_le_fieldOver' A K (1 * q) hz', isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨z, hz'⟩)⟩
        have : (⟨_, h⟩ : ↥(jIntegralClosure (1 * q) A K)) = ⟨y, hyC⟩ + ⟨z, hzC⟩ := rfl
        rw [this, map_add]; exact add_mem (ihy hyC) (ihz hzC)
    | neg y hy' ihy =>
        intro h
        have hyC : y ∈ jIntegralClosure (1 * q) A K := ⟨jRing_le_fieldOver' A K (1 * q) hy', isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨y, hy'⟩)⟩
        have : (⟨_, h⟩ : ↥(jIntegralClosure (1 * q) A K)) = -⟨y, hyC⟩ := rfl
        rw [this, map_neg]; exact neg_mem (ihy hyC)
    | mul y z hy' hz' ihy ihz =>
        intro h
        have hyC : y ∈ jIntegralClosure (1 * q) A K := ⟨jRing_le_fieldOver' A K (1 * q) hy', isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨y, hy'⟩)⟩
        have hzC : z ∈ jIntegralClosure (1 * q) A K := ⟨jRing_le_fieldOver' A K (1 * q) hz', isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨z, hz'⟩)⟩
        have : (⟨_, h⟩ : ↥(jIntegralClosure (1 * q) A K)) = ⟨y, hyC⟩ * ⟨z, hzC⟩ := rfl
        rw [this, map_mul]; exact mul_mem (ihy hyC) (ihz hzC)
  rintro _ ⟨c, rfl⟩
  have hc : c ∈ Submodule.span ↥(jRing A K) (T : Set ↥(jIntegralClosure (1 * q) A K)) := by rw [hT]; trivial
  induction hc using Submodule.span_induction with
  | mem t ht => exact IntermediateField.subset_adjoin _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem σ ht))
  | zero => rw [map_zero]; exact zero_mem E
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ?_ hx
      exact hJ r r.2 _

end Finiteness
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

end NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

namespace FiniteFieldEmb

theorem mem_range_of_ringHom {κ M : Type*} [Field κ] [Fintype κ] [Field M] [DecidableEq M]
    (ι₁ ι₂ : κ →+* M) (x : κ) : ι₂ x ∈ ι₁.range := by
  classical

  set n := Fintype.card κ with hn
  have hn1 : 1 < n := Fintype.one_lt_card
  let P : Polynomial M := Polynomial.X ^ n - Polynomial.X
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero M hn1
  have hdeg : P.natDegree = n := FiniteField.X_pow_card_sub_X_natDegree_eq M hn1
  have hroot : ∀ (ι : κ →+* M) (y : κ), ι y ∈ P.roots := by
    intro ι y
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, ← map_pow, FiniteField.pow_card, sub_self]

  have hcard : (Finset.univ.image ι₁).card = n := by
    rw [Finset.card_image_of_injective _ ι₁.injective, Finset.card_univ]
  have hsub : Finset.univ.image ι₁ ⊆ P.roots.toFinset := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    exact Multiset.mem_toFinset.mpr (hroot ι₁ x)
  have hle : P.roots.toFinset.card ≤ n := by
    calc P.roots.toFinset.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = n := hdeg
  have heq : Finset.univ.image ι₁ = P.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have : ι₂ x ∈ P.roots.toFinset := Multiset.mem_toFinset.mpr (hroot ι₂ x)
  rw [← heq, Finset.mem_image] at this
  obtain ⟨y, -, hy⟩ := this
  exact ⟨y, hy⟩

theorem exists_eq_comp_pow {κ M : Type*} [Field κ] [Finite κ] [Field M]
    (p : ℕ) [Fact p.Prime] [CharP κ p] (ι₁ ι₂ : κ →+* M) :
    ∃ m : ℕ, ∀ x : κ, ι₂ x = ι₁ (x ^ (p ^ m)) := by
  classical
  haveI := Fintype.ofFinite κ

  let e : κ ≃+* ι₁.range := RingEquiv.ofBijective ι₁.rangeRestrict
    ⟨fun a b h => ι₁.injective (congrArg Subtype.val h), ι₁.rangeRestrict_surjective⟩
  let ι₂' : κ →+* ι₁.range := ι₂.codRestrict ι₁.range (mem_range_of_ringHom ι₁ ι₂)
  let σ : κ →+* κ := e.symm.toRingHom.comp ι₂'
  have hσ : ∀ x, ι₁ (σ x) = ι₂ x := by
    intro x
    have h1 : ((e (σ x) : ι₁.range) : M) = ι₁ (σ x) := rfl
    rw [← h1]
    change ((e (e.symm (ι₂' x)) : ι₁.range) : M) = ι₂ x
    rw [e.apply_symm_apply]; rfl

  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  haveI : Algebra.IsAlgebraic (ZMod p) κ := Algebra.IsAlgebraic.of_finite (ZMod p) κ
  have hcomm : ∀ r : ZMod p, σ (algebraMap (ZMod p) κ r) = algebraMap (ZMod p) κ r := by
    intro r
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective r
    rw [map_natCast, map_natCast]
  let σₐ : κ →ₐ[ZMod p] κ := { σ with commutes' := hcomm }
  let σₑ : κ ≃ₐ[ZMod p] κ := AlgEquiv.ofBijective σₐ (σₐ.toRingHom.injective.bijective_of_finite)
  obtain ⟨⟨m, hm⟩, hmσ⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) κ).2 σₑ
  refine ⟨m, fun x => ?_⟩
  rw [← hσ x]
  congr 1
  change σₑ x = _
  rw [← hmσ, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

end FiniteFieldEmb
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries jqModC jqNModC ModularPolynomialData transcendental_jqModC minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing jIntegralClosure pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve.NodeLocalized"

section Main

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem mem_nonunits_iff_of_forall_mem_iff' (A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ))
    (L : IntermediateField ↥K (AlgebraicClosure ℚ))
    (τ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ)
    (hτ : ∀ x : AlgebraicClosure ℚ, x ∈ L → (x ∈ A₁ ↔ τ x ∈ A₂)) (x : AlgebraicClosure ℚ) (hx : x ∈ L) :
    x ∈ A₁.nonunits ↔ τ x ∈ A₂.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    map_eq_zero_iff τ τ.injective, ← map_inv₀, ← hτ _ (L.inv_mem hx)]

set_option maxHeartbeats 12800000 in

theorem main {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (a : k) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭)
    (h𝔭S : ∀ s : MvPolynomial (Fin 2) ↥(coeffSubring A K), pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0 →
      ∀ hs : modularEval (1 * q) (coeffSubring A K) s ∈ jIntegralClosure (1 * q) A K,
        (⟨_, hs⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭) :
    ∃ σ : ↥(jIntegralClosure (1 * q) A K) →+* AlgebraicClosure ℚ,
      RingHom.ker σ = 𝔭 ∧
      (∀ (b : ↥(coeffSubring A K)) (hb : CharPReduction.constSeries (coeffSubring A K) b ∈ jIntegralClosure (1 * q) A K),
          σ ⟨_, hb⟩ = b) ∧
      (∀ hj : jqModC (AlgebraicClosure ℚ) ∈ jIntegralClosure (1 * q) A K,
          ∃ hjA : σ ⟨_, hj⟩ ∈ A, red ⟨_, hjA⟩ = a) ∧
      (∀ hj' : jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ jIntegralClosure (1 * q) A K,
          ∃ hjA : σ ⟨_, hj'⟩ ∈ A, red ⟨_, hjA⟩ = a ^ q) := by
  classical
  have hqprime : q.Prime := Fact.out

  obtain ⟨𝔐, h𝔐max, θ, h𝔭𝔐, hkerθ, hθ⟩ := exists_maximal_ringHom_algClosure A K red a 𝔭 h𝔭 hq𝔭 h𝔭S
  obtain ⟨σ₀, hker₀, hσ₀K⟩ := exists_ringHom_ker_eq A K red 𝔭 h𝔭 hq𝔭
  obtain ⟨A'', hA''C, hA''𝔐⟩ :=
    exists_valuationSubring_dominating 𝔐 h𝔐max.ne_top σ₀ (hker₀ ▸ h𝔭𝔐)

  have hq𝔐 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∈ 𝔐 := by
    rw [← hkerθ, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hqA'' : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A''.nonunits := by
    have := hA''𝔐 _ hq𝔐; rwa [map_natCast] at this
  have hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    exact ⟨(q : A).2, by
      have : (⟨((q : ℕ) : AlgebraicClosure ℚ), (q : A).2⟩ : A) = (q : A) := Subtype.ext rfl
      rw [this]; exact not_isUnit_natCast q red⟩

  have hle : ∀ x : AlgebraicClosure ℚ, x ∈ K → x ∈ A → x ∈ A'' := by
    intro x hxK hxA
    let b : ↥(coeffSubring A K) := ⟨x, (mem_coeffSubring_iff' A K).mpr ⟨hxA, hxK⟩⟩
    have := hA''C ⟨_, constSeries_mem_jIntegralClosure A K b⟩
    rwa [hσ₀K] at this

  let L₀ : IntermediateField ↥K (AlgebraicClosure ℚ) := IntermediateField.adjoin ↥K (Set.range σ₀)
  haveI : FiniteDimensional ↥K L₀ := finiteDimensional_adjoin_range A K σ₀ hσ₀K
  have hmemL₀ : ∀ c, σ₀ c ∈ L₀ := fun c => IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩
  obtain ⟨τ, hτ⟩ := ValuationSubring.exists_algEquiv_forall_mem_iff_of_nonunits K A A'' hle hqprime hqA hqA'' L₀
  let σ₁ : ↥(jIntegralClosure (1 * q) A K) →+* AlgebraicClosure ℚ := (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp σ₀
  have hσ₁A : ∀ c, σ₁ c ∈ A := fun c => (hτ _ (hmemL₀ c)).mp (hA''C c)
  have hσ₁𝔐 : ∀ c ∈ 𝔐, σ₁ c ∈ A.nonunits := fun c hc =>
    (mem_nonunits_iff_of_forall_mem_iff' K A'' A L₀ τ hτ _ (hmemL₀ c)).mp (hA''𝔐 c hc)
  have hσ₁K : ∀ (b : ↥(coeffSubring A K)) (hb : CharPReduction.constSeries (coeffSubring A K) b ∈ jIntegralClosure (1 * q) A K),
      σ₁ ⟨_, hb⟩ = b := fun b hb => by
    change τ (σ₀ ⟨_, hb⟩) = b
    rw [hσ₀K]
    exact τ.commutes (⟨(b : AlgebraicClosure ℚ), ((mem_coeffSubring_iff' A K).mp b.2).2⟩ : ↥K)
  have hker₁ : RingHom.ker σ₁ = 𝔭 := by
    ext c; rw [RingHom.mem_ker, ← hker₀, RingHom.mem_ker]
    change τ (σ₀ c) = 0 ↔ _
    rw [map_eq_zero_iff τ τ.injective]

  let ρ : ↥(jIntegralClosure (1 * q) A K) →+* k :=
    red.comp ((σ₁.codRestrict A.toSubring hσ₁A))
  have hρ : ∀ c, ρ c = red ⟨σ₁ c, hσ₁A c⟩ := fun _ => rfl
  have hkerρ : RingHom.ker ρ = 𝔐 := by
    refine (h𝔐max.eq_of_le (RingHom.ker_ne_top ρ) fun c hc => ?_).symm
    rw [RingHom.mem_ker, hρ, ← RingHom.mem_ker, ker_red_eq_maximalIdeal A q red]
    have := hσ₁𝔐 c hc
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at this
    obtain ⟨h, hm⟩ := this
    exact hm

  let L₁ : IntermediateField ↥K (AlgebraicClosure ℚ) := IntermediateField.adjoin ↥K (Set.range σ₁)
  haveI : FiniteDimensional ↥K L₁ := finiteDimensional_adjoin_range A K σ₁ hσ₁K
  have hmemL₁ : ∀ c, σ₁ c ∈ L₁ := fun c => IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩
  haveI : 𝔐.IsMaximal := h𝔐max
  letI : Field (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔐) := Ideal.Quotient.field 𝔐

  let θbar : (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔐) →+* AlgebraicClosure k :=
    Ideal.Quotient.lift 𝔐 θ (fun c hc => by rw [← RingHom.mem_ker, hkerθ]; exact hc)
  have hθbar : ∀ c, θbar (Ideal.Quotient.mk 𝔐 c) = θ c := fun c => Ideal.Quotient.lift_mk _ _ _
  haveI : CharP (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔐) q := (θbar.charP_iff_charP q).mpr inferInstance

  have hσ₁𝔐' : ∀ c ∈ 𝔐, (⟨σ₁ c, hσ₁A c⟩ : A) ∈ IsLocalRing.maximalIdeal ↥A := by
    intro c hc
    have := hσ₁𝔐 c hc
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at this
    obtain ⟨h, hm⟩ := this
    exact hm
  let ρbar : (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔐) →+* AlgebraicClosure k :=
    Ideal.Quotient.lift 𝔐 ((algebraMap k (AlgebraicClosure k)).comp ρ) (fun c hc => by
      rw [RingHom.comp_apply, hρ]
      have : red ⟨σ₁ c, hσ₁A c⟩ = 0 := by
        rw [← RingHom.mem_ker, ker_red_eq_maximalIdeal A q red]; exact hσ₁𝔐' c hc
      rw [this, map_zero])
  have hρbar : ∀ c, ρbar (Ideal.Quotient.mk 𝔐 c) = algebraMap k (AlgebraicClosure k) (red ⟨σ₁ c, hσ₁A c⟩) :=
    fun c => Ideal.Quotient.lift_mk _ _ _

  let rA : (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔐) →+* IsLocalRing.ResidueField ↥A :=
    Ideal.Quotient.lift 𝔐 ((IsLocalRing.residue ↥A).comp (σ₁.codRestrict A.toSubring hσ₁A)) (fun c hc => by
      rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
      exact hσ₁𝔐' c hc)
  have hrA : ∀ c, rA (Ideal.Quotient.mk 𝔐 c) = IsLocalRing.residue ↥A ⟨σ₁ c, hσ₁A c⟩ :=
    fun c => Ideal.Quotient.lift_mk _ _ _

  haveI : Finite (↥(jIntegralClosure (1 * q) A K) ⧸ 𝔐) := by
    have hfin := ValuationSubring.finite_range_residue_of_nonunits K A hqprime hqA L₁
    let S := Set.range fun x : {x : AlgebraicClosure ℚ // x ∈ L₁ ∧ x ∈ A} => IsLocalRing.residue ↥A ⟨x.1, x.2.2⟩
    haveI : Finite S := hfin.to_subtype
    have hmemS : ∀ y : ↥(jIntegralClosure (1 * q) A K) ⧸ 𝔐, rA y ∈ S := by
      intro y
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨⟨σ₁ c, hmemL₁ c, hσ₁A c⟩, (hrA c).symm⟩
    refine Finite.of_injective (fun y : ↥(jIntegralClosure (1 * q) A K) ⧸ 𝔐 => (⟨rA y, hmemS y⟩ : S)) ?_
    intro y₁ y₂ h
    exact rA.injective (congrArg Subtype.val h)

  obtain ⟨m, hm⟩ := FiniteFieldEmb.exists_eq_comp_pow q θbar ρbar

  have hfix : ∀ (x : AlgebraicClosure ℚ) (hxK : x ∈ K) (hxA : x ∈ A),
      IsLocalRing.residue ↥A ⟨x, hxA⟩ ^ (q ^ m) = IsLocalRing.residue ↥A ⟨x, hxA⟩ := by
    intro x hxK hxA
    let b : ↥(coeffSubring A K) := ⟨x, (mem_coeffSubring_iff' A K).mpr ⟨hxA, hxK⟩⟩
    let cb : ↥(jIntegralClosure (1 * q) A K) := ⟨_, constSeries_mem_jIntegralClosure A K b⟩
    have hσcb : σ₁ cb = x := hσ₁K b _
    have hAcb : (⟨σ₁ cb, hσ₁A cb⟩ : A) = ⟨x, hxA⟩ := Subtype.ext hσcb

    have hθcb : θ cb = algebraMap k (AlgebraicClosure k) (redRestrict red K b) := by
      have h2 : cb = ⟨_, modularEval_mem_jIntegralClosure A K (MvPolynomial.C b)⟩ :=
        Subtype.ext (by change _ = modularEval _ _ _; unfold modularEval; rw [MvPolynomial.eval₂Hom_C])
      rw [h2, hθ]; unfold pointEval; rw [MvPolynomial.eval₂Hom_C]
    have h1 : θbar ((Ideal.Quotient.mk 𝔐 cb) ^ (q ^ m)) = θbar (Ideal.Quotient.mk 𝔐 cb) := by
      rw [← hm, hρbar, hθbar, hθcb, hAcb]
      rfl
    have h2 : (Ideal.Quotient.mk 𝔐 cb) ^ (q ^ m) = Ideal.Quotient.mk 𝔐 cb := θbar.injective h1
    have h3 := congrArg rA h2
    rw [map_pow, hrA, hAcb] at h3
    exact h3

  obtain ⟨δ, hδA, hδres⟩ :=
    ValuationSubring.exists_algEquiv_residue_pow_eq_of_nonunits K A hqprime hqA L₁ m hfix

  let redbar : IsLocalRing.ResidueField ↥A →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥A) red (fun x hx => by
      rw [← RingHom.mem_ker, ker_red_eq_maximalIdeal A q red]; exact hx)
  have hredbar : ∀ x : A, redbar (IsLocalRing.residue ↥A x) = red x := fun x => Ideal.Quotient.lift_mk _ _ _

  have hkey : ∀ (c : ↥(jIntegralClosure (1 * q) A K)) (hδc : δ (σ₁ c) ∈ A) (t : k),
      θ c = algebraMap k (AlgebraicClosure k) t → red ⟨δ (σ₁ c), hδc⟩ = t := by
    intro c hδc t ht
    have e1 := hδres (σ₁ c) (hmemL₁ c) (hσ₁A c) hδc
    have e2 := congrArg redbar e1
    rw [map_pow, hredbar, hredbar] at e2

    have e3 : algebraMap k (AlgebraicClosure k) (red ⟨σ₁ c, hσ₁A c⟩)
        = (algebraMap k (AlgebraicClosure k) t) ^ (q ^ m) := by
      rw [← hρbar, hm, ← map_pow, hθbar, map_pow, ht]
    rw [← map_pow, (algebraMap k (AlgebraicClosure k)).injective.eq_iff] at e3
    rw [e3] at e2

    have : (red ⟨δ (σ₁ c), hδc⟩ - t) ^ (q ^ m) = 0 := by rw [sub_pow_char_pow, e2, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero m hqprime.ne_zero) |>.mp this)
  refine ⟨(δ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp σ₁, ?_, ?_, ?_, ?_⟩
  · ext c
    rw [RingHom.mem_ker, ← hker₁, RingHom.mem_ker]
    change δ (σ₁ c) = 0 ↔ σ₁ c = 0
    rw [map_eq_zero_iff δ δ.injective]
  · intro b hb
    change δ (σ₁ ⟨_, hb⟩) = b
    rw [hσ₁K]
    exact δ.commutes (⟨(b : AlgebraicClosure ℚ), ((mem_coeffSubring_iff' A K).mp b.2).2⟩ : ↥K)
  · intro hj
    have hδj : δ (σ₁ ⟨_, hj⟩) ∈ A := (hδA _ (hmemL₁ _)).mp (hσ₁A _)
    refine ⟨hδj, hkey _ hδj a ?_⟩
    have h2 : (⟨_, hj⟩ : ↥(jIntegralClosure (1 * q) A K)) = ⟨_, modularEval_mem_jIntegralClosure A K (MvPolynomial.X 0)⟩ :=
      Subtype.ext (by change _ = modularEval _ _ _; unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl)
    rw [h2, hθ]; unfold pointEval; rw [MvPolynomial.eval₂Hom_X']; rfl
  · intro hj'
    have hδj : δ (σ₁ ⟨_, hj'⟩) ∈ A := (hδA _ (hmemL₁ _)).mp (hσ₁A _)
    refine ⟨hδj, hkey _ hδj (a ^ q) ?_⟩
    have h2 : (⟨_, hj'⟩ : ↥(jIntegralClosure (1 * q) A K)) = ⟨_, modularEval_mem_jIntegralClosure A K (MvPolynomial.X 1)⟩ :=
      Subtype.ext (by change _ = modularEval _ _ _; unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl)
    rw [h2, hθ]; unfold pointEval; rw [MvPolynomial.eval₂Hom_X']; rfl

end Main
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

end NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem.ModularCurve"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭)
    (h𝔭S : ∀ s : MvPolynomial (Fin 2) ↥(coeffSubring A K), pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0 →
      ∀ hs : modularEval (1 * q) (coeffSubring A K) s ∈ jIntegralClosure (1 * q) A K, (⟨_, hs⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭) :
    ∃ σ : ↥(jIntegralClosure (1 * q) A K) →+* AlgebraicClosure ℚ,
      RingHom.ker σ = 𝔭 ∧
      (∀ (b : ↥(coeffSubring A K)) (hb : CharPReduction.constSeries (coeffSubring A K) b ∈ jIntegralClosure (1 * q) A K),
          σ ⟨_, hb⟩ = b) ∧
      (∀ hj : jqModC (AlgebraicClosure ℚ) ∈ jIntegralClosure (1 * q) A K,
          ∃ hjA : σ ⟨_, hj⟩ ∈ A, red ⟨_, hjA⟩ = a) ∧
      (∀ hj' : jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ jIntegralClosure (1 * q) A K,
          ∃ hjA : σ ⟨_, hj'⟩ ∈ A, red ⟨_, hjA⟩ = a ^ q) := by
  exact ModularCurve.NodeLocalized.main A K red a 𝔭 h𝔭 hq𝔭 h𝔭S

end S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem (solution)
