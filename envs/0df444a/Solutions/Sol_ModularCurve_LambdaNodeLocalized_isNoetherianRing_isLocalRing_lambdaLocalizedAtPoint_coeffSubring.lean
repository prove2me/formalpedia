-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/cdba4438-1660-5394-a8ce-07b5951e3a21

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero
import Theorems.Thm_ModularCurve_exists_lambdaKroneckerCongruence
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"
set_option autoImplicit false
set_option maxHeartbeats 3200000

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve.LambdaNodeLocalized"
open MvPolynomial

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "NodeLocalized.pointEval NodeLocalized.sub_C_eval_mem_span NodeLocalized.ker_pointEval_eq_span LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two LambdaNodeLocalized.isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing LambdaNodeLocalized.exists_ne_zero_lambdaEval_eq_zero exists_lambdaKroneckerCongruence"
p2m_open "ModularCurve"
namespace LambdaNodeLocalized
p2m_export "ModularCurve.LambdaNodeLocalized" "lambdaEval lambdaLocalizedAtPoint lambdaEval_mem_lambdaLocalizedAtPoint pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint exists_ne_zero_lambdaEval_eq_zero"
p2m_open "ModularCurve.LambdaNodeLocalized"

open MvPolynomial

section Presentation

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)

def lambdaEvalAt : MvPolynomial (Fin 2) A →+* lambdaLocalizedAtPoint N A red a b :=
  (lambdaEval N A).codRestrict _ (lambdaEval_mem_lambdaLocalizedAtPoint N A red a b)

@[scoped simp] theorem coe_lambdaEvalAt (p : MvPolynomial (Fin 2) A) :
    (lambdaEvalAt N A red a b p : LaurentSeries L) = lambdaEval N A p := rfl

abbrev evalRange : Subring (LaurentSeries L) := (lambdaEval N A).range

theorem evalRange_le : evalRange N A ≤ lambdaLocalizedAtPoint N A red a b := by
  rintro _ ⟨p, rfl⟩
  exact lambdaEval_mem_lambdaLocalizedAtPoint N A red a b p

scoped instance algebraEvalRange : Algebra (evalRange N A) (lambdaLocalizedAtPoint N A red a b) :=
  (Subring.inclusion (evalRange_le N A red a b)).toAlgebra

theorem algebraMap_evalRange_coe (y : evalRange N A) :
    ((algebraMap (evalRange N A) (lambdaLocalizedAtPoint N A red a b) y : lambdaLocalizedAtPoint N A red a b) :
      LaurentSeries L) = y := rfl

theorem algebraMap_evalRange_rangeRestrict (p : MvPolynomial (Fin 2) A) :
    algebraMap (evalRange N A) (lambdaLocalizedAtPoint N A red a b) ((lambdaEval N A).rangeRestrict p)
      = lambdaEvalAt N A red a b p := rfl

def nodeDenominators : Submonoid (evalRange N A) where
  carrier := {y | ∃ s : MvPolynomial (Fin 2) A, NodeLocalized.pointEval A red a b s ≠ 0 ∧ (lambdaEval N A).rangeRestrict s = y}
  one_mem' := ⟨1, by rw [map_one]; exact one_ne_zero, by rw [map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, by rw [map_mul]⟩

theorem rangeRestrict_mem_nodeDenominators {s : MvPolynomial (Fin 2) A} (hs : NodeLocalized.pointEval A red a b s ≠ 0) :
    (lambdaEval N A).rangeRestrict s ∈ nodeDenominators N A red a b :=
  ⟨s, hs, rfl⟩

theorem mem_nodeDenominators_iff (y : evalRange N A) :
    y ∈ nodeDenominators N A red a b ↔ ∃ s : MvPolynomial (Fin 2) A, NodeLocalized.pointEval A red a b s ≠ 0 ∧ lambdaEval N A s = y := by
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, Subtype.ext h⟩

section KerLE

variable [hker : Fact (RingHom.ker (lambdaEval N A) ≤ RingHom.ker (NodeLocalized.pointEval A red a b))]

theorem lambdaEval_ne_zero_of_pointEval_ne_zero {s : MvPolynomial (Fin 2) A} (hs : NodeLocalized.pointEval A red a b s ≠ 0) :
    lambdaEval N A s ≠ 0 := fun h => hs (hker.out ((RingHom.mem_ker).mpr h))

theorem isUnit_lambdaEvalAt {s : MvPolynomial (Fin 2) A} (hs : NodeLocalized.pointEval A red a b s ≠ 0) :
    IsUnit (lambdaEvalAt N A red a b s) := by
  have hs0 := lambdaEval_ne_zero_of_pointEval_ne_zero N A red a b hs
  refine isUnit_iff_exists_inv.mpr ⟨⟨(lambdaEval N A s)⁻¹, 1, s, hs, ?_⟩, Subtype.ext ?_⟩
  · rw [map_one, inv_mul_cancel₀ hs0]
  · exact mul_inv_cancel₀ hs0

scoped instance isLocalization_nodeDenominators :
    IsLocalization (nodeDenominators N A red a b) (lambdaLocalizedAtPoint N A red a b) where
  map_units := by
    rintro ⟨_, s, hs, rfl⟩
    rw [algebraMap_evalRange_rangeRestrict]
    exact isUnit_lambdaEvalAt N A red a b hs
  surj := fun z => by
    obtain ⟨r, s, hs, h⟩ := z.2
    exact ⟨⟨(lambdaEval N A).rangeRestrict r, ⟨(lambdaEval N A).rangeRestrict s,
      rangeRestrict_mem_nodeDenominators N A red a b hs⟩⟩, Subtype.ext h⟩
  exists_of_eq := fun {x y} h => ⟨1, by
    simp only [OneMemClass.coe_one, one_mul]
    exact Subtype.ext (congrArg (fun w : lambdaLocalizedAtPoint N A red a b => (w : LaurentSeries L)) h)⟩

scoped instance isLocalRing_lambdaLocalizedAtPoint : IsLocalRing (lambdaLocalizedAtPoint N A red a b) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨r, s, hs, h⟩ := z.2
  have hs0 := lambdaEval_ne_zero_of_pointEval_ne_zero N A red a b hs
  have hz : (z : LaurentSeries L) = lambdaEval N A r * (lambdaEval N A s)⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  by_cases hr : NodeLocalized.pointEval A red a b r = 0
  · right
    have hsr : NodeLocalized.pointEval A red a b (s - r) ≠ 0 := by rw [map_sub, hr, sub_zero]; exact hs
    have hsr0 := lambdaEval_ne_zero_of_pointEval_ne_zero N A red a b hsr
    have hsr0' : lambdaEval N A s - lambdaEval N A r ≠ 0 := by rwa [map_sub] at hsr0
    refine isUnit_iff_exists_inv.mpr ⟨⟨lambdaEval N A s * (lambdaEval N A (s - r))⁻¹, s, s - r, hsr, ?_⟩, Subtype.ext ?_⟩
    · rw [mul_assoc, inv_mul_cancel₀ hsr0, mul_one]
    · show (1 - (z : LaurentSeries L)) * (lambdaEval N A s * (lambdaEval N A (s - r))⁻¹) = 1
      rw [hz, map_sub]
      field_simp
  · left
    have hr0 := lambdaEval_ne_zero_of_pointEval_ne_zero N A red a b hr
    refine isUnit_iff_exists_inv.mpr ⟨⟨lambdaEval N A s * (lambdaEval N A r)⁻¹, s, r, hr, ?_⟩, Subtype.ext ?_⟩
    · rw [mul_assoc, inv_mul_cancel₀ hr0, mul_one]
    · show (z : LaurentSeries L) * (lambdaEval N A s * (lambdaEval N A r)⁻¹) = 1
      rw [hz]
      field_simp

end KerLE

end Presentation

end LambdaNodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve.LambdaNodeLocalized"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "NodeLocalized.pointEval NodeLocalized.sub_C_eval_mem_span NodeLocalized.ker_pointEval_eq_span LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two LambdaNodeLocalized.isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing LambdaNodeLocalized.exists_ne_zero_lambdaEval_eq_zero exists_lambdaKroneckerCongruence"
p2m_open "ModularCurve"
namespace LambdaNodeLocalized
p2m_export "ModularCurve.LambdaNodeLocalized" "lambdaEval lambdaLocalizedAtPoint lambdaEval_mem_lambdaLocalizedAtPoint pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint exists_ne_zero_lambdaEval_eq_zero"
p2m_open "ModularCurve.LambdaNodeLocalized"
namespace N1

theorem isDVR {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] [CharP k q] [FiniteDimensional ℚ K] :
    IsDiscreteValuationRing ↥(coeffSubring A K) := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso
    have hqK : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
      rw [h]; exact (K.inv_mem (natCast_mem K q) : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ K)
    have h1 : redRestrict red K ((q : ℕ) : ↥(coeffSubring A K)) * redRestrict red K ⟨_, hqK⟩ = 1 := by
      rw [← map_mul, ← map_one (redRestrict red K)]
      congr 1
      apply Subtype.ext
      push_cast
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    rw [map_natCast, CharP.cast_eq_zero, zero_mul] at h1
    exact zero_ne_one h1
  · exact h

variable {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  {k : Type*} [Field k] [CharP k q] (red : A →+* k) (l : k)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem exists_ne_zero_lambdaEval_eq_zero' (hq2 : q ≠ 2) :
    ∃ P : MvPolynomial (Fin 2) ↥(coeffSubring A K), P ≠ 0 ∧ lambdaEval q (coeffSubring A K) P = 0 := by
  obtain ⟨data, -⟩ := ModularCurve.exists_lambdaKroneckerCongruence q hq2
  exact ModularCurve.LambdaNodeLocalized.exists_ne_zero_lambdaEval_eq_zero data (coeffSubring A K)

section Main
variable [FiniteDimensional ℚ K] [DecidableEq k]

theorem main (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = l)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    IsNoetherianRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ∧ IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ∧ ringKrullDim ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) = 2 ∧
    (∀ [IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))], IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) =
      Ideal.span {lambdaEvalAt q (coeffSubring A K) (redRestrict red K) l (l ^ q) (MvPolynomial.C ϖ), lambdaEvalAt q (coeffSubring A K) (redRestrict red K) l (l ^ q) (MvPolynomial.X 0 - MvPolynomial.C x),
        lambdaEvalAt q (coeffSubring A K) (redRestrict red K) l (l ^ q) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))}) := by
  classical
  haveI hfact : Fact (RingHom.ker (lambdaEval q (coeffSubring A K)) ≤
      RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q))) :=
    ⟨fun s hs => (RingHom.mem_ker).mpr
      (ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red l hl2 K s ((RingHom.mem_ker).mp hs))⟩
  haveI : IsDiscreteValuationRing ↥(coeffSubring A K) := isDVR red K q
  set φ := lambdaEval q (coeffSubring A K) with hφ
  set pe := pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) with hpe
  set E := lambdaEvalAt q (coeffSubring A K) (redRestrict red K) l (l ^ q) with hEdef
  set ρ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(evalRange q (coeffSubring A K)) := φ.rangeRestrict with hρ
  have hρsurj : Function.Surjective ρ := RingHom.rangeRestrict_surjective φ
  have hkerρ : RingHom.ker ρ = RingHom.ker φ := RingHom.ker_rangeRestrict φ
  have hEρ : (algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))).comp ρ = E := RingHom.ext fun _ => rfl

  haveI : IsNoetherianRing ↥(evalRange q (coeffSubring A K)) := isNoetherianRing_of_surjective _ _ ρ hρsurj
  have hnoeth : IsNoetherianRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) :=
    IsLocalization.isNoetherianRing (nodeDenominators q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _ ‹_›
  have hloc : IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) := inferInstance

  haveI : (RingHom.ker pe).IsPrime := RingHom.ker_isPrime pe
  set P : Ideal ↥(evalRange q (coeffSubring A K)) := (RingHom.ker pe).map ρ with hP
  haveI hPp : P.IsPrime := Ideal.map_isPrime_of_surjective hρsurj (by rw [hkerρ]; exact hfact.out)
  have hM : nodeDenominators q (coeffSubring A K) (redRestrict red K) l (l ^ q) = P.primeCompl := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩ hy
      obtain ⟨s', hs', hss'⟩ := (Ideal.mem_map_iff_of_surjective ρ hρsurj).mp hy
      have hd : s - s' ∈ RingHom.ker φ := by
        rw [← hkerρ, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hss'.symm
      have : s ∈ RingHom.ker pe := by simpa using (RingHom.ker pe).add_mem (hfact.out hd) hs'
      exact hs ((RingHom.mem_ker).mp this)
    · intro hy
      obtain ⟨s, rfl⟩ := hρsurj y
      refine ⟨s, fun hs0 => hy (Ideal.mem_map_of_mem ρ ((RingHom.mem_ker).mpr hs0)), rfl⟩
  haveI : IsLocalization.AtPrime (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) P := by
    show IsLocalization P.primeCompl _
    rw [← hM]; infer_instance

  have hker : RingHom.ker pe = Ideal.span {MvPolynomial.C ϖ, MvPolynomial.X 0 - MvPolynomial.C x,
      MvPolynomial.X 1 - MvPolynomial.C (x ^ q)} :=
    ker_pointEval_eq_span (coeffSubring A K) (redRestrict red K) l (l ^ q) x (x ^ q) hx (by rw [map_pow, hx]) ϖ hϖ
  have hmaxEq : IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) =
      Ideal.span {E (MvPolynomial.C ϖ), E (MvPolynomial.X 0 - MvPolynomial.C x), E (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), hP, Ideal.map_map, hEρ, hker, Ideal.map_span,
      Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

  obtain ⟨PhiT, hΦ0, hΦk'⟩ := exists_ne_zero_lambdaEval_eq_zero' A K hq2
  have hΦk : PhiT ∈ RingHom.ker φ := (RingHom.mem_ker).mpr hΦk'
  have hdimS : ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K)) = 3 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one, Nat.card_fin]; rfl
  have h1 : ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ Ideal.span {PhiT}) + 1 ≤ 3 :=
    hdimS ▸ ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hΦ0)
  have h2 : ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ RingHom.ker φ) ≤ ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ Ideal.span {PhiT}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor
      ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hΦk)))) (Ideal.Quotient.factor_surjective _)
  have h3 : ringKrullDim ↥(evalRange q (coeffSubring A K)) = ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ RingHom.ker φ) :=
    (ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivRange φ)).symm

  have hRR : ringKrullDim ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≤ ringKrullDim ↥(evalRange q (coeffSubring A K)) := by
    refine Order.krullDim_le_of_strictMono
      (fun p : PrimeSpectrum ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) =>
        (⟨p.asIdeal.comap (algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))), inferInstance⟩ : PrimeSpectrum ↥(evalRange q (coeffSubring A K)))) ?_
    intro p p' hlt
    refine lt_of_le_of_ne (Ideal.comap_mono hlt.le) ?_
    intro heq
    apply hlt.ne
    apply PrimeSpectrum.ext
    have heq' : Ideal.comap (algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) p.asIdeal
        = Ideal.comap (algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) p'.asIdeal :=
      congrArg PrimeSpectrum.asIdeal heq
    have hmc1 : Ideal.map (algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))))
        (Ideal.comap (algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) p.asIdeal) = p.asIdeal :=
      IsLocalization.map_comap (nodeDenominators q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) p.asIdeal
    have hmc2 : Ideal.map (algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))))
        (Ideal.comap (algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) p'.asIdeal) = p'.asIdeal :=
      IsLocalization.map_comap (nodeDenominators q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) p'.asIdeal
    rw [← hmc1, ← hmc2, heq']
  have hup : ringKrullDim ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) + 1 ≤ 3 := by
    have : ringKrullDim ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≤ ringKrullDim (MvPolynomial (Fin 2) ↥(coeffSubring A K) ⧸ Ideal.span {PhiT}) :=
      hRR.trans (h3 ▸ h2)
    exact (add_le_add this le_rfl).trans h1

  obtain ⟨⟨hp1, -, hnot⟩, -⟩ :=
    ModularCurve.LambdaNodeLocalized.isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint hq2 red l hl2 K ϖ hϖ
  set 𝔭₁ : Ideal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) := Ideal.span {E (MvPolynomial.C ϖ), E (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)} with h𝔭₁
  haveI : 𝔭₁.IsPrime := hp1
  have hϖ0 : E (MvPolynomial.C ϖ) ≠ 0 := by
    intro h
    have h1 : (ϖ : AlgebraicClosure ℚ) = 0 := by
      have := congrArg (fun w : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) => (w : LaurentSeries (AlgebraicClosure ℚ))) h
      change lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ) = 0 at this
      rw [lambdaEval, MvPolynomial.eval₂Hom_C] at this
      change algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ) = 0 at this
      exact (map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective).mp this
    have h2 : ϖ = 0 := Subtype.ext h1
    have h3 : redRestrict red K ((q : ℕ) : ↥(coeffSubring A K)) = 0 := by rw [map_natCast, CharP.cast_eq_zero]
    obtain ⟨d, hd⟩ := (hϖ _).mp h3
    rw [h2, zero_mul] at hd
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
      (by have := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hd; push_cast at this; exact this)
  have hbot : (⊥ : Ideal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) < 𝔭₁ :=
    bot_lt_iff_ne_bot.mpr fun h => hϖ0 (by
      have : E (MvPolynomial.C ϖ) ∈ 𝔭₁ := Ideal.subset_span (Set.mem_insert _ _)
      rw [h] at this; exact (Submodule.mem_bot _).mp this)
  have hlt : 𝔭₁ < IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp1.ne_top) fun h => hnot x ?_
    change E (MvPolynomial.X 0 - MvPolynomial.C x) ∈ 𝔭₁
    rw [h, hmaxEq]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hlow : (2 : WithBot ℕ∞) ≤ ringKrullDim ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) := by
    let p0 : PrimeSpectrum ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) := ⟨⊥, Ideal.bot_prime⟩
    let p1 : PrimeSpectrum ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) := ⟨𝔭₁, hp1⟩
    let p2 : PrimeSpectrum ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) := ⟨IsLocalRing.maximalIdeal _, inferInstance⟩
    have h01 : p0 < p1 := hbot
    have h12 : p1 < p2 := hlt
    let s : LTSeries (PrimeSpectrum ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) :=
      { length := 2
        toFun := ![p0, p1, p2]
        step := fun i => by
          fin_cases i
          · exact h01
          · exact h12 }
    calc (2 : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by norm_num
      _ = (s.length : WithBot ℕ∞) := rfl
      _ ≤ _ := Order.LTSeries.length_le_krullDim s
  have hdim : ringKrullDim ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) = 2 := by
    have hup' : ringKrullDim ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≤ 2 := by
      revert hup
      generalize ringKrullDim ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) = d
      intro hup
      induction d using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe e =>
        induction e using ENat.recTopCoe with
        | top => exact absurd hup (by decide)
        | coe m =>
          have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((3 : ℕ) : WithBot ℕ∞) := by simpa using hup
          have h3' : m + 1 ≤ 3 := by exact_mod_cast h'
          have hm : (m : ℕ∞) ≤ 2 := by exact_mod_cast (by omega : m ≤ 2)
          exact WithBot.coe_le_coe.mpr hm
    exact le_antisymm hup' hlow
  exact ⟨hnoeth, hloc, hdim, fun {_} => hmaxEq⟩

end Main
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve"

end N1
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve"
end LambdaNodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve ModularCurve.NodeLocalized _root_.ModularCurve.LambdaNodeLocalized _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve.LambdaNodeLocalized in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (l : k) (hl2 : l ^ (q ^ 2) = l)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = l)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    IsNoetherianRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ∧
    IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ∧
    ringKrullDim ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) = 2 ∧
    (∀ [IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))],
      IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) =
        Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
          (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
          (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))}) :=
  ModularCurve.LambdaNodeLocalized.N1.main A red l K hq2 hl2 x hx ϖ hϖ

end
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring.ModularCurve"

end S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring (solution)
