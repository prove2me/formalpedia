-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/77363dda-d60d-56b5-9ed4-4c1e5ee1df07

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_eval2_branch_eq_zero_of_lambdaEval_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve.LambdaNodeLocalized"
open MvPolynomial

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "NodeLocalized.pointEval NodeLocalized.sub_C_eval_mem_span NodeLocalized.ker_pointEval_eq_span LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero"
p2m_open "ModularCurve"
namespace LambdaNodeLocalized
p2m_export "ModularCurve.LambdaNodeLocalized" "lambdaEval lambdaLocalizedAtPoint lambdaEval_mem_lambdaLocalizedAtPoint pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two eval2_branch_eq_zero_of_lambdaEval_eq_zero"
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
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve.LambdaNodeLocalized"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "NodeLocalized.pointEval NodeLocalized.sub_C_eval_mem_span NodeLocalized.ker_pointEval_eq_span LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero"
p2m_open "ModularCurve"
namespace LambdaNodeLocalized
p2m_export "ModularCurve.LambdaNodeLocalized" "lambdaEval lambdaLocalizedAtPoint lambdaEval_mem_lambdaLocalizedAtPoint pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two eval2_branch_eq_zero_of_lambdaEval_eq_zero"
p2m_open "ModularCurve.LambdaNodeLocalized"
namespace Branch

variable {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] (red : A →+* k) (l : k) (hl2 : l ^ (q ^ 2) = l)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ))

local notation "Ψ₀" => MvPolynomial.eval₂Hom (Polynomial.C.comp (redRestrict red K))
  ![(Polynomial.X : Polynomial k), Polynomial.X ^ q]
local notation "Ψ₁" => MvPolynomial.eval₂Hom (Polynomial.C.comp (redRestrict red K))
  ![(Polynomial.X : Polynomial k) ^ q, Polynomial.X]

section Taylor
variable (B : Type*) [CommRing B]

noncomputable abbrev ι₀ : Polynomial B →+* MvPolynomial (Fin 2) B := Polynomial.eval₂RingHom C (X 0)

noncomputable abbrev ι₁ : Polynomial B →+* MvPolynomial (Fin 2) B := Polynomial.eval₂RingHom C (X 1)

noncomputable abbrev σ₀ (q : ℕ) : MvPolynomial (Fin 2) B →+* Polynomial B := eval₂Hom Polynomial.C ![Polynomial.X, Polynomial.X ^ q]

noncomputable abbrev σ₁ (q : ℕ) : MvPolynomial (Fin 2) B →+* Polynomial B := eval₂Hom Polynomial.C ![Polynomial.X ^ q, Polynomial.X]

omit [Fact q.Prime] in
theorem sub_ι₀_σ₀_mem (s : MvPolynomial (Fin 2) B) :
    s - ι₀ B (σ₀ B q s) ∈ Ideal.span {(X 1 : MvPolynomial (Fin 2) B) - X 0 ^ q} := by
  induction s using MvPolynomial.induction_on with
  | C c =>
    rw [coe_eval₂Hom, eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, sub_self]; exact zero_mem _
  | add p r hp hr =>
    have : p + r - ι₀ B (σ₀ B q (p + r)) = (p - ι₀ B (σ₀ B q p)) + (r - ι₀ B (σ₀ B q r)) := by
      rw [map_add, map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p j hp =>
    have key : p * X j - ι₀ B (σ₀ B q (p * X j))
        = (p - ι₀ B (σ₀ B q p)) * X j + ι₀ B (σ₀ B q p) * (X j - ι₀ B (![Polynomial.X, Polynomial.X ^ q] j)) := by
      rw [map_mul, map_mul, coe_eval₂Hom, eval₂_X]; ring
    rw [key]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    fin_cases j <;> simp [Polynomial.coe_eval₂RingHom]

omit [Fact q.Prime] in
theorem sub_ι₁_σ₁_mem (s : MvPolynomial (Fin 2) B) :
    s - ι₁ B (σ₁ B q s) ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) B) - X 1 ^ q} := by
  induction s using MvPolynomial.induction_on with
  | C c =>
    rw [coe_eval₂Hom, eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, sub_self]; exact zero_mem _
  | add p r hp hr =>
    have : p + r - ι₁ B (σ₁ B q (p + r)) = (p - ι₁ B (σ₁ B q p)) + (r - ι₁ B (σ₁ B q r)) := by
      rw [map_add, map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p j hp =>
    have key : p * X j - ι₁ B (σ₁ B q (p * X j))
        = (p - ι₁ B (σ₁ B q p)) * X j + ι₁ B (σ₁ B q p) * (X j - ι₁ B (![Polynomial.X ^ q, Polynomial.X] j)) := by
      rw [map_mul, map_mul, coe_eval₂Hom, eval₂_X]; ring
    rw [key]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    fin_cases j <;> simp [Polynomial.coe_eval₂RingHom]

end Taylor
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve"

section Kernels
variable (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)

omit [CharP k q] in
theorem ψ₀_eq : Ψ₀ = (Polynomial.mapRingHom (redRestrict red K)).comp (σ₀ _ q) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · simp [Polynomial.coe_mapRingHom]
  · fin_cases j <;> simp [Polynomial.coe_mapRingHom]

omit [CharP k q] in
theorem ψ₁_eq : Ψ₁ = (Polynomial.mapRingHom (redRestrict red K)).comp (σ₁ _ q) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · simp [Polynomial.coe_mapRingHom]
  · fin_cases j <;> simp [Polynomial.coe_mapRingHom]

omit [CharP k q] in
include hϖ in

theorem C_dvd_of_map_eq_zero (P : Polynomial ↥(coeffSubring A K)) (hP : P.map (redRestrict red K) = 0) :
    Polynomial.C ϖ ∣ P := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro n
  have hn := congrArg (fun Q => Polynomial.coeff Q n) hP
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hn
  obtain ⟨d, hd⟩ := (hϖ _).mp hn
  exact ⟨d, hd⟩

omit [CharP k q] in
include hϖ in
theorem mem_span₀_iff (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    s ∈ Ideal.span {C ϖ, (X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 0 ^ q} ↔ Ψ₀ s = 0 := by
  constructor
  · intro hs
    have hle : Ideal.span {C ϖ, (X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 0 ^ q} ≤ RingHom.ker Ψ₀ := by
      rw [Ideal.span_le]
      rintro _ (rfl | rfl)
      · rw [SetLike.mem_coe, RingHom.mem_ker, eval₂Hom_C, RingHom.comp_apply, (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩, map_zero]
      · rw [SetLike.mem_coe, RingHom.mem_ker]; simp
    exact (RingHom.mem_ker).mp (hle hs)
  · intro hs
    rw [ψ₀_eq, RingHom.comp_apply, Polynomial.coe_mapRingHom] at hs
    obtain ⟨t, ht⟩ := C_dvd_of_map_eq_zero red K ϖ hϖ _ hs
    have : s = (s - ι₀ _ (σ₀ _ q s)) + ι₀ _ (σ₀ _ q s) := by ring
    rw [this]
    refine add_mem (Ideal.span_mono (Set.subset_insert _ _) (sub_ι₀_σ₀_mem _ s)) ?_
    rw [ht, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

omit [CharP k q] in
include hϖ in
theorem mem_span₁_iff (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    s ∈ Ideal.span {C ϖ, (X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 1 ^ q} ↔ Ψ₁ s = 0 := by
  constructor
  · intro hs
    have hle : Ideal.span {C ϖ, (X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 1 ^ q} ≤ RingHom.ker Ψ₁ := by
      rw [Ideal.span_le]
      rintro _ (rfl | rfl)
      · rw [SetLike.mem_coe, RingHom.mem_ker, eval₂Hom_C, RingHom.comp_apply, (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩, map_zero]
      · rw [SetLike.mem_coe, RingHom.mem_ker]; simp
    exact (RingHom.mem_ker).mp (hle hs)
  · intro hs
    rw [ψ₁_eq, RingHom.comp_apply, Polynomial.coe_mapRingHom] at hs
    obtain ⟨t, ht⟩ := C_dvd_of_map_eq_zero red K ϖ hϖ _ hs
    have : s = (s - ι₁ _ (σ₁ _ q s)) + ι₁ _ (σ₁ _ q s) := by ring
    rw [this]
    refine add_mem (Ideal.span_mono (Set.subset_insert _ _) (sub_ι₁_σ₁_mem _ s)) ?_
    rw [ht, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

theorem eval_ψ₀ (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    (Ψ₀ s).eval l = pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) s := by
  rw [← Polynomial.coe_evalRingHom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom, pointEval]
  congr 2
  · ext c; simp
  · funext i; fin_cases i <;> simp

theorem eval_ψ₁ (ha2 : l ^ (q ^ 2) = l) (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    (Ψ₁ s).eval (l ^ q) = pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) s := by
  rw [← Polynomial.coe_evalRingHom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom, pointEval]
  congr 2
  · ext c; simp
  · funext i; fin_cases i
    · simp only [Matrix.cons_val_zero, Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X,
        Fin.zero_eta]
      rw [← pow_mul, show q * q = q ^ 2 from (sq q).symm, ha2]
    · simp

omit [CharP k q] in
theorem X_sub_X_pow_pow_ne_zero : (Polynomial.X : Polynomial k) - (Polynomial.X ^ q) ^ q ≠ 0 := by
  rw [← pow_mul]
  intro h
  have h1 := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
  rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] at h1
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  nlinarith

end Kernels
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve"

include hq2 hl2 in
theorem main (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    let E := lambdaEvalAt q (coeffSubring A K) (redRestrict red K) l (l ^ q)
    ((Ideal.span {E (C ϖ), E (X 1 - X 0 ^ q)}).IsPrime ∧ E (X 0 - X 1 ^ q) ∉ Ideal.span {E (C ϖ), E (X 1 - X 0 ^ q)} ∧
      ∀ c : ↥(coeffSubring A K), E (X 0 - C c) ∉ Ideal.span {E (C ϖ), E (X 1 - X 0 ^ q)}) ∧
    (l ^ (q ^ 2) = l →
      (Ideal.span {E (C ϖ), E (X 0 - X 1 ^ q)}).IsPrime ∧ E (X 1 - X 0 ^ q) ∉ Ideal.span {E (C ϖ), E (X 0 - X 1 ^ q)}) := by
  classical
  intro E
  haveI hfact : Fact (RingHom.ker (lambdaEval q (coeffSubring A K)) ≤
      RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q))) :=
    ⟨fun s hs => (RingHom.mem_ker).mpr
      (ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red l hl2 K s ((RingHom.mem_ker).mp hs))⟩
  set φ := lambdaEval q (coeffSubring A K) with hφ
  set pe := pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) with hpe
  set ρ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(evalRange q (coeffSubring A K)) := φ.rangeRestrict with hρ
  have hE : ∀ p, E p = algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (ρ p) := fun p => rfl
  have hEmap : ∀ J : Ideal (MvPolynomial (Fin 2) ↥(coeffSubring A K)),
      J.map E = (J.map ρ).map (algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) := fun J => by
    rw [Ideal.map_map]; congr 1
  have hkerρ : RingHom.ker ρ = RingHom.ker φ := RingHom.ker_rangeRestrict φ
  have hρsurj : Function.Surjective ρ := RingHom.rangeRestrict_surjective φ
  have hinj : Function.Injective (algebraMap (↥(evalRange q (coeffSubring A K))) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) := fun u v huv =>
    Subtype.ext (congrArg (fun w : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) => (w : LaurentSeries (AlgebraicClosure ℚ))) huv)

  have prime_of : ∀ J : Ideal (MvPolynomial (Fin 2) ↥(coeffSubring A K)),
      J.IsPrime → RingHom.ker φ ≤ J → J ≤ RingHom.ker pe → (J.map E).IsPrime := by
    intro J hJ hkJ hJn
    rw [hEmap]
    have hP : (J.map ρ).IsPrime := Ideal.map_isPrime_of_surjective hρsurj (by rw [hkerρ]; exact hkJ)
    refine IsLocalization.isPrime_of_isPrime_disjoint (nodeDenominators q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) _ hP ?_
    rw [Set.disjoint_left]
    rintro y ⟨s, hs, rfl⟩ hy
    obtain ⟨s', hs', hss'⟩ := (Ideal.mem_map_iff_of_surjective ρ hρsurj).mp hy
    have hd : s - s' ∈ RingHom.ker φ := by
      rw [← hkerρ, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hss'.symm
    have hsJ : s ∈ J := by simpa using J.add_mem (hkJ hd) hs'
    exact hs ((RingHom.mem_ker).mp (hJn hsJ))

  have not_mem_of : ∀ (J : Ideal (MvPolynomial (Fin 2) ↥(coeffSubring A K))) (ψ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* Polynomial k),
      (∀ s, s ∈ J ↔ ψ s = 0) → RingHom.ker φ ≤ J → (∀ s, ψ s = 0 → pe s = 0) →
      ∀ h₀, ψ h₀ ≠ 0 → E h₀ ∉ J.map E := by
    intro J ψ hJ hkJ hψpe h₀ hh₀ hmem
    rw [hEmap, hE] at hmem
    obtain ⟨⟨⟨y, hy⟩, ⟨m, hm⟩⟩, hrel⟩ := (IsLocalization.mem_map_algebraMap_iff (nodeDenominators q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))).mp hmem
    obtain ⟨s, hs, rfl⟩ := hm
    obtain ⟨s', hs', rfl⟩ := (Ideal.mem_map_iff_of_surjective ρ hρsurj).mp hy
    have hρeq : ρ (h₀ * s) = ρ s' := hinj (by rw [map_mul, map_mul]; exact hrel)
    have hdiff : h₀ * s - s' ∈ RingHom.ker φ := by
      rw [← hkerρ, RingHom.mem_ker, map_sub, hρeq, sub_self]
    have hJs : h₀ * s ∈ J := by simpa using J.add_mem (hkJ hdiff) hs'
    have h1 : ψ h₀ * ψ s = 0 := by rw [← map_mul]; exact (hJ _).mp hJs
    rcases mul_eq_zero.mp h1 with h | h
    · exact hh₀ h
    · exact hs (hψpe s h)

  have hk0 : RingHom.ker φ ≤ Ideal.span {C ϖ, (X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 0 ^ q} :=
    fun s hs => (mem_span₀_iff red K ϖ hϖ s).mpr
      (ModularCurve.LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero hq2 red K s ((RingHom.mem_ker).mp hs)).1
  have hk1 : RingHom.ker φ ≤ Ideal.span {C ϖ, (X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 1 ^ q} :=
    fun s hs => (mem_span₁_iff red K ϖ hϖ s).mpr
      (ModularCurve.LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero hq2 red K s ((RingHom.mem_ker).mp hs)).2
  have hmap0 : (Ideal.span {C ϖ, (X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 0 ^ q}).map E
      = Ideal.span {E (C ϖ), E (X 1 - X 0 ^ q)} := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  have hmap1 : (Ideal.span {C ϖ, (X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 1 ^ q}).map E
      = Ideal.span {E (C ϖ), E (X 0 - X 1 ^ q)} := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  refine ⟨⟨?_, ?_, fun c => ?_⟩, fun ha2 => ⟨?_, ?_⟩⟩
  · rw [← hmap0]
    refine prime_of _ ?_ hk0 (fun s hs => ?_)
    · have : Ideal.span {C ϖ, (X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 0 ^ q} = RingHom.ker Ψ₀ := by
        ext s; rw [RingHom.mem_ker]; exact mem_span₀_iff red K ϖ hϖ s
      rw [this]; exact RingHom.ker_isPrime _
    · rw [RingHom.mem_ker, ← eval_ψ₀, (mem_span₀_iff red K ϖ hϖ s).mp hs, Polynomial.eval_zero]
  · rw [← hmap0]
    refine not_mem_of _ Ψ₀ (mem_span₀_iff red K ϖ hϖ) hk0 (fun s hs => by rw [hpe, ← eval_ψ₀, hs, Polynomial.eval_zero]) _ ?_
    rw [map_sub, map_pow]
    simp only [eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one]
    exact X_sub_X_pow_pow_ne_zero
  · rw [← hmap0]
    refine not_mem_of _ Ψ₀ (mem_span₀_iff red K ϖ hϖ) hk0 (fun s hs => by rw [hpe, ← eval_ψ₀, hs, Polynomial.eval_zero]) _ ?_
    rw [map_sub, eval₂Hom_C, RingHom.comp_apply]
    simp only [eval₂Hom_X', Matrix.cons_val_zero]
    intro h
    have h1 := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_zero] at h1
    exact one_ne_zero h1
  · rw [← hmap1]
    refine prime_of _ ?_ hk1 (fun s hs => ?_)
    · have : Ideal.span {C ϖ, (X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) - X 1 ^ q} = RingHom.ker Ψ₁ := by
        ext s; rw [RingHom.mem_ker]; exact mem_span₁_iff red K ϖ hϖ s
      rw [this]; exact RingHom.ker_isPrime _
    · rw [RingHom.mem_ker, ← eval_ψ₁ red l K ha2, (mem_span₁_iff red K ϖ hϖ s).mp hs, Polynomial.eval_zero]
  · rw [← hmap1]
    refine not_mem_of _ Ψ₁ (mem_span₁_iff red K ϖ hϖ) hk1 (fun s hs => by rw [hpe, ← eval_ψ₁ red l K ha2, hs, Polynomial.eval_zero]) _ ?_
    rw [map_sub, map_pow]
    simp only [eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one]
    exact X_sub_X_pow_pow_ne_zero

end Branch
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve"
end LambdaNodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve ModularCurve.NodeLocalized _root_.ModularCurve.LambdaNodeLocalized _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve.LambdaNodeLocalized in

theorem solution
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (l : k) (hl2 : l ^ (q ^ 2) = l)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ((Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
        (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))}).IsPrime ∧
      (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∉ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ∧
      ∀ c : ↥(coeffSubring A K), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C c),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∉ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))}) ∧
    (l ^ (q ^ 2) = l →
      (Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
          (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))}).IsPrime ∧
      (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∉ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))}) :=
  ModularCurve.LambdaNodeLocalized.Branch.main hq2 red l hl2 K ϖ hϖ

end
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint.ModularCurve"

end S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint (solution)
