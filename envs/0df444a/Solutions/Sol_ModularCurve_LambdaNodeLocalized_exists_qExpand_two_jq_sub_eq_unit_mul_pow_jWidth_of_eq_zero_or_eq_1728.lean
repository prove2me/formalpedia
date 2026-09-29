-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_qExpand_two_jq_sub_eq_unit_mul_pow_jWidth_of_eq_zero_or_eq_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/de0661c3-33f0-5866-abcc-bf8ca20fe13e

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_qExpand_two_jq_sub_eq_unit_mul_pow_jWidth_of_eq_zero_or_eq_1728
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_qExpand_two_jq_sub_eq_unit_mul_pow_jWidth_of_eq_zero_or_eq_1728.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap jWidth jWidth_of_eq_zero jWidth_of_eq_1728 qExpand_two_jq_mul_lambdaModC_sq LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two"
p2m_open "ModularCurve"
namespace JRamAssembly

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

section Defs
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (l : k)
  (K : IntermediateField ℚ Qb)

abbrev S : Subring LQ := lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)

def E : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(S q A red l K) :=
  (lambdaEval q (coeffSubring A K)).codRestrict (S q A red l K)
    (lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))

theorem E_apply (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    E q A red l K p = ⟨lambdaEval q (coeffSubring A K) p,
      lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) p⟩ := rfl

theorem coe_E (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    ((E q A red l K p : ↥(S q A red l K)) : LQ) = lambdaEval q (coeffSubring A K) p := rfl

abbrev pe : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* k := pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q)

theorem pe_C (c : ↥(coeffSubring A K)) : pe q A red l K (MvPolynomial.C c) = redRestrict red K c :=
  MvPolynomial.eval₂Hom_C _ _ c

theorem pe_X (i : Fin 2) : pe q A red l K (MvPolynomial.X i) = ![l, l ^ q] i :=
  MvPolynomial.eval₂Hom_X' _ _ i

end Defs

section FieldFacts
variable (q : ℕ) [Fact q.Prime]

omit [Fact q.Prime] in

theorem qExpand_algebraMap (N : ℕ) [NeZero N] (c : Qb) :
    qExpand Qb N (algebraMap Qb LQ c) = algebraMap Qb LQ c := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

omit [Fact q.Prime] in

theorem jLambda_Qb :
    qExpand Qb 2 (jqModC Qb) * lambdaModC Qb ^ 2 * (16 * lambdaModC Qb - 1) ^ 2
      = (256 * lambdaModC Qb ^ 2 - 16 * lambdaModC Qb + 1) ^ 3 := by
  have h := congrArg (laurentMap (algebraMap ℚ Qb)) ModularCurve.qExpand_two_jq_mul_lambdaModC_sq
  have hj : laurentMap (algebraMap ℚ Qb) jq = jqModC Qb := by
    rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ Qb)
  have hμ : laurentMap (algebraMap ℚ Qb) (lambdaModC ℚ) = lambdaModC Qb := by
    rw [lambdaModC, lambdaModC, laurentMap_laurentMap]
    exact congrArg (fun g => laurentMap g lambdaInt) (RingHom.ext_int _ _)
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, laurentMap_qExpand, hj, hμ, map_ofNat] using h

theorem jLambda_Qb_q :
    qExpand Qb 2 (jqNModC Qb (1 * q)) * lambdaNModC Qb q ^ 2 * (16 * lambdaNModC Qb q - 1) ^ 2
      = (256 * lambdaNModC Qb q ^ 2 - 16 * lambdaNModC Qb q + 1) ^ 3 := by
  have h := congrArg (qExpand Qb q) (jLambda_Qb)
  have hj : qExpand Qb q (qExpand Qb 2 (jqModC Qb)) = qExpand Qb 2 (jqNModC Qb (1 * q)) := by
    rw [jqNModC, qExpand_qExpand, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hj, lambdaNModC] using h

theorem lambdaEval_X0 {A : ValuationSubring Qb} (K : IntermediateField ℚ Qb) :
    lambdaEval q (coeffSubring A K) (MvPolynomial.X 0) = lambdaModC Qb := by
  simp [lambdaEval]

theorem lambdaEval_X1 {A : ValuationSubring Qb} (K : IntermediateField ℚ Qb) :
    lambdaEval q (coeffSubring A K) (MvPolynomial.X 1) = lambdaNModC Qb q := by
  simp [lambdaEval]

end FieldFacts

section Core
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]
  (red : A →+* k) (l : k) (K : IntermediateField ℚ Qb)

omit [DecidableEq k] in

theorem isUnit_E_of_pe_ne_zero (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l)
    (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) (hs : pe q A red l K s ≠ 0) :
    IsUnit (E q A red l K s) := by
  have h0 : lambdaEval q (coeffSubring A K) s ≠ 0 := fun h =>
    hs (ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red l hl2 K s h)
  refine isUnit_iff_exists_inv.mpr ⟨⟨(lambdaEval q (coeffSubring A K) s)⁻¹, 1, s, hs, ?_⟩, ?_⟩
  · rw [map_one]; exact inv_mul_cancel₀ h0
  · exact Subtype.ext (mul_inv_cancel₀ h0)

omit [DecidableEq k] in
theorem two_ne_zero_of_five_le (hq : 5 ≤ q) : (2 : k) ≠ 0 := by
  rw [show (2 : k) = ((2 : ℕ) : k) by norm_cast, Ne, CharP.cast_eq_zero_iff k q]
  intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega

omit [DecidableEq k] in
theorem three_ne_zero_of_five_le (hq : 5 ≤ q) : (3 : k) ≠ 0 := by
  rw [show (3 : k) = ((3 : ℕ) : k) by norm_cast, Ne, CharP.cast_eq_zero_iff k q]
  intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega

theorem core (hq : 5 ≤ q) (hl2 : l ^ (q ^ 2) = l)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (i : Fin 2) (ll aa : k) (hll : pe q A red l K (MvPolynomial.X i) = ll)
    (h01728 : aa = 0 ∨ aa = 1728) (hl0 : ll ≠ 0) (hl1 : 16 * ll ≠ 1)
    (hla : aa * ((16 * ll) ^ 2 * (16 * ll - 1) ^ 2) = 256 * ((16 * ll) ^ 2 - 16 * ll + 1) ^ 3)
    (xx yy : ↥(coeffSubring A K)) (hxx : redRestrict red K xx = aa) (hyy : redRestrict red K yy = ll) :
    ∃ (u : (↥(S q A red l K))ˣ) (c d : ↥(S q A red l K)),
      (u : ↥(S q A red l K)) = E q A red l K (MvPolynomial.X i ^ 2 * (16 * MvPolynomial.X i - 1) ^ 2) ∧ IsUnit c ∧
      E q A red l K ((256 * MvPolynomial.X i ^ 2 - 16 * MvPolynomial.X i + 1) ^ 3) * ↑u⁻¹
          - E q A red l K (MvPolynomial.C xx)
        = c * E q A red l K (MvPolynomial.X i - MvPolynomial.C yy) ^ jWidth aa
          + E q A red l K (MvPolynomial.C ϖ) * d := by
  classical
  have hq2 : q ≠ 2 := by omega
  have h2 : (2 : k) ≠ 0 := two_ne_zero_of_five_le (k := k) (q := q) hq
  have h3 : (3 : k) ≠ 0 := three_ne_zero_of_five_le (k := k) (q := q) hq
  set Ev := E q A red l K with hEv
  set μ := Ev (MvPolynomial.X i) with hμ
  set Y := Ev (MvPolynomial.C yy) with hY
  set ϖ' := Ev (MvPolynomial.C ϖ) with hϖ'

  have hDn : IsUnit (Ev (MvPolynomial.X i ^ 2 * (16 * MvPolynomial.X i - 1) ^ 2)) := by
    apply isUnit_E_of_pe_ne_zero red l K hq2 hl2
    simp only [map_mul, map_pow, map_sub, map_ofNat, map_one, hll]
    exact mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ (sub_ne_zero.mpr hl1))
  obtain ⟨u, hu⟩ := hDn

  have hred : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 →
      ∃ t : ↥(S q A red l K), Ev (MvPolynomial.C c) = ϖ' * t := by
    intro c hc
    obtain ⟨d, rfl⟩ := (hϖ c).mp hc
    exact ⟨Ev (MvPolynomial.C d), by rw [map_mul, map_mul]⟩
  rcases h01728 with haa | haa
  ·
    subst haa
    have h256 : (256 : k) ≠ 0 := by
      have : (256 : k) = 2 ^ 8 := by norm_num
      rw [this]; exact pow_ne_zero _ h2
    have hD : (16 * ll) ^ 2 - 16 * ll + 1 = 0 := by
      have h0 : 256 * ((16 * ll) ^ 2 - 16 * ll + 1) ^ 3 = 0 := by rw [← hla]; ring
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp h0).resolve_left h256)

    have hβ : IsUnit (Ev (256 * (MvPolynomial.X i + MvPolynomial.C yy) - 16)) := by
      apply isUnit_E_of_pe_ne_zero red l K hq2 hl2
      simp only [map_sub, map_mul, map_add, map_ofNat, hll, pe_C, hyy]
      intro h0
      have h768 : (768 : k) ≠ 0 := by
        have : (768 : k) = 2 ^ 8 * 3 := by norm_num
        rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) h3
      apply h768
      linear_combination (1024 : k) * hD - (256 * (ll + ll) - 16) * h0
    obtain ⟨t, ht⟩ := hred (256 * yy ^ 2 - 16 * yy + 1) (by
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, hyy]
      linear_combination hD)
    obtain ⟨s, hs⟩ := hred xx hxx
    obtain ⟨β, hβ'⟩ := hβ
    refine ⟨u, ↑(β ^ 3 * u⁻¹),
      (3 * ((μ - Y) * ↑β) ^ 2 * t + 3 * ((μ - Y) * ↑β) * ϖ' * t ^ 2 + ϖ' ^ 2 * t ^ 3) * ↑u⁻¹ - s,
      hu, Units.isUnit _, ?_⟩
    rw [jWidth_of_eq_zero (rfl : (0 : k) = 0)]
    have hN : Ev (256 * MvPolynomial.X i ^ 2 - 16 * MvPolynomial.X i + 1) = (μ - Y) * ↑β + ϖ' * t := by
      have e1 : Ev (256 * MvPolynomial.X i ^ 2 - 16 * MvPolynomial.X i + 1)
          = (μ - Y) * Ev (256 * (MvPolynomial.X i + MvPolynomial.C yy) - 16)
            + Ev (MvPolynomial.C (256 * yy ^ 2 - 16 * yy + 1)) := by
        simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, hμ, hY]; ring
      rw [e1, ← hβ', ht]
    rw [map_pow, hN, hs, Units.val_mul, Units.val_pow_eq_pow_val, map_sub, ← hμ, ← hY]
    ring
  ·
    subst haa
    have h1728 : (1728 : k) ≠ 0 := by
      have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
      rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
    have h256 : (256 : k) ≠ 0 := by
      have : (256 : k) = 2 ^ 8 := by norm_num
      rw [this]; exact pow_ne_zero _ h2

    have hP : 4096 * ll ^ 3 - 384 * ll ^ 2 - 24 * ll + 1 = 0 := by
      have h0 : 256 * (4096 * ll ^ 3 - 384 * ll ^ 2 - 24 * ll + 1) ^ 2 = 0 := by
        linear_combination (-1 : k) * hla
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp h0).resolve_left h256)

    have hQ : IsUnit (Ev (4096 * (MvPolynomial.X i ^ 2 + MvPolynomial.X i * MvPolynomial.C yy + MvPolynomial.C yy ^ 2)
        - 384 * (MvPolynomial.X i + MvPolynomial.C yy) - 24)) := by
      apply isUnit_E_of_pe_ne_zero red l K hq2 hl2
      simp only [map_sub, map_mul, map_add, map_pow, map_ofNat, hll, pe_C, hyy]
      intro h0
      have h216 : (216 : k) ≠ 0 := by
        have : (216 : k) = 2 ^ 3 * 3 ^ 3 := by norm_num
        rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
      apply h216
      linear_combination (96 - 3072 * ll) * hP + (1024 * ll ^ 2 - 64 * ll - 5) * h0
    obtain ⟨t, ht⟩ := hred (4096 * yy ^ 3 - 384 * yy ^ 2 - 24 * yy + 1) (by
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, hyy]
      linear_combination hP)
    obtain ⟨s, hs⟩ := hred (xx - 1728) (by rw [map_sub, map_ofNat, hxx, sub_self])
    obtain ⟨Q, hQ'⟩ := hQ
    refine ⟨u, ↑(Q ^ 2 * u⁻¹), (2 * ((μ - Y) * ↑Q) * t + ϖ' * t ^ 2) * ↑u⁻¹ - s, hu, Units.isUnit _, ?_⟩
    rw [jWidth_of_eq_1728 rfl h1728]

    have hP1 : Ev (4096 * MvPolynomial.X i ^ 3 - 384 * MvPolynomial.X i ^ 2 - 24 * MvPolynomial.X i + 1)
        = (μ - Y) * ↑Q + ϖ' * t := by
      have e1 : Ev (4096 * MvPolynomial.X i ^ 3 - 384 * MvPolynomial.X i ^ 2 - 24 * MvPolynomial.X i + 1)
          = (μ - Y) * Ev (4096 * (MvPolynomial.X i ^ 2 + MvPolynomial.X i * MvPolynomial.C yy + MvPolynomial.C yy ^ 2)
              - 384 * (MvPolynomial.X i + MvPolynomial.C yy) - 24)
            + Ev (MvPolynomial.C (4096 * yy ^ 3 - 384 * yy ^ 2 - 24 * yy + 1)) := by
        simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, hμ, hY]; ring
      rw [e1, ← hQ', ht]

    have hN3 : Ev ((256 * MvPolynomial.X i ^ 2 - 16 * MvPolynomial.X i + 1) ^ 3)
        = ((μ - Y) * ↑Q + ϖ' * t) ^ 2 + 1728 * ↑u := by
      rw [← hP1, hu]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, hμ]
      ring
    have hxx' : Ev (MvPolynomial.C xx) = 1728 + ϖ' * s := by
      rw [← hs]; simp only [map_sub, map_ofNat]; ring
    have huu : (u : ↥(S q A red l K)) * ↑u⁻¹ = 1 := u.mul_inv
    rw [hN3, hxx', Units.val_mul, Units.val_pow_eq_pow_val, map_sub, ← hμ, ← hY]
    linear_combination (1728 : ↥(S q A red l K)) * huu

end Core

end JRamAssembly
end ModularCurve

end

open ModularCurve.JRamAssembly in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (h01728 : a = 0 ∨ a = 1728)
    (l : k) (hl2 : l ^ (q ^ 2) = l) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ∃ (J Jq c cq d dq : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
      (J : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) 2 (jqModC (AlgebraicClosure ℚ)) ∧
      (Jq : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) 2 (jqNModC (AlgebraicClosure ℚ) (1 * q)) ∧
      IsUnit c ∧ IsUnit cq ∧
      J - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C x),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) =
        c * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ^ jWidth a +
          (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * d ∧
      Jq - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C (x ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) =
        cq * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ^ jWidth a +
          (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * dq := by
  classical
  have hq2 : q ≠ 2 := by omega
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero

  set φ : k →+* k := frobenius k q with hφ
  have hφl : φ l = l ^ q := frobenius_def ..
  have haq : a ^ q = a := by
    rcases h01728 with rfl | rfl
    · exact zero_pow hq0
    · exact (frobenius_def ..).symm.trans (map_ofNat φ 1728)
  have hφa : φ a = a := by rw [hφ, frobenius_def, haq]
  have hla' : a * ((16 * l ^ q) ^ 2 * (16 * l ^ q - 1) ^ 2) = 256 * ((16 * l ^ q) ^ 2 - 16 * l ^ q + 1) ^ 3 := by
    have h := congrArg φ hla
    simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, map_one, hφl, hφa] at h
    linear_combination h
  have hl0' : l ^ q ≠ 0 := pow_ne_zero _ hl0
  have hl1' : 16 * l ^ q ≠ 1 := by
    intro h
    apply hl1
    have h1 : φ (16 * l) = φ 1 := by rw [map_mul, map_ofNat, hφl, map_one, h]
    exact frobenius_inj k q h1
  have hx' : redRestrict red K (x ^ q) = a := by rw [map_pow, hx, haq]
  have hy' : redRestrict red K (y ^ q) = l ^ q := by rw [map_pow, hy]
  have hll0 : pe q A red l K (MvPolynomial.X 0) = l := by rw [pe_X]; rfl
  have hll1 : pe q A red l K (MvPolynomial.X 1) = l ^ q := by rw [pe_X]; rfl
  obtain ⟨u, c, d, hu, hc, h⟩ := core red l K hq hl2 ϖ hϖ 0 l a hll0 h01728 hl0 hl1 hla x y hx hy
  obtain ⟨u', c', d', hu', hc', h'⟩ := core red l K hq hl2 ϖ hϖ 1 (l ^ q) a hll1 h01728 hl0' hl1' hla'
    (x ^ q) (y ^ q) hx' hy'
  refine ⟨E q A red l K ((256 * MvPolynomial.X 0 ^ 2 - 16 * MvPolynomial.X 0 + 1) ^ 3) * ↑u⁻¹,
    E q A red l K ((256 * MvPolynomial.X 1 ^ 2 - 16 * MvPolynomial.X 1 + 1) ^ 3) * ↑u'⁻¹,
    c, c', d, d', ?_, ?_, hc, hc', ?_, ?_⟩
  ·
    have hD : ((u : ↥(S q A red l K)) : LaurentSeries (AlgebraicClosure ℚ))
        = lambdaModC (AlgebraicClosure ℚ) ^ 2 * (16 * lambdaModC (AlgebraicClosure ℚ) - 1) ^ 2 := by
      rw [hu, coe_E]; simp only [map_mul, map_pow, map_sub, map_ofNat, map_one, lambdaEval_X0]
    have hinv : (((u⁻¹ : (↥(S q A red l K))ˣ) : ↥(S q A red l K)) : LaurentSeries (AlgebraicClosure ℚ))
        * ((u : ↥(S q A red l K)) : LaurentSeries (AlgebraicClosure ℚ)) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Subring.coe_one]
    have hD0 := right_ne_zero_of_mul_eq_one hinv
    have hN : lambdaEval q (coeffSubring A K) ((256 * MvPolynomial.X 0 ^ 2 - 16 * MvPolynomial.X 0 + 1) ^ 3)
        = (256 * lambdaModC (AlgebraicClosure ℚ) ^ 2 - 16 * lambdaModC (AlgebraicClosure ℚ) + 1) ^ 3 := by
      simp only [map_pow, map_add, map_sub, map_mul, map_ofNat, map_one, lambdaEval_X0]
    have hD0' : lambdaModC (AlgebraicClosure ℚ) ^ 2 * (16 * lambdaModC (AlgebraicClosure ℚ) - 1) ^ 2 ≠ 0 := hD ▸ hD0
    rw [Subring.coe_mul, coe_E, hN, eq_inv_of_mul_eq_one_left hinv, hD]
    exact ((eq_mul_inv_iff_mul_eq₀ hD0').mpr (by rw [← mul_assoc]; exact jLambda_Qb)).symm
  ·
    have hD : ((u' : ↥(S q A red l K)) : LaurentSeries (AlgebraicClosure ℚ))
        = lambdaNModC (AlgebraicClosure ℚ) q ^ 2 * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) ^ 2 := by
      rw [hu', coe_E]; simp only [map_mul, map_pow, map_sub, map_ofNat, map_one, lambdaEval_X1]
    have hinv : (((u'⁻¹ : (↥(S q A red l K))ˣ) : ↥(S q A red l K)) : LaurentSeries (AlgebraicClosure ℚ))
        * ((u' : ↥(S q A red l K)) : LaurentSeries (AlgebraicClosure ℚ)) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Subring.coe_one]
    have hD0 := right_ne_zero_of_mul_eq_one hinv
    have hN : lambdaEval q (coeffSubring A K) ((256 * MvPolynomial.X 1 ^ 2 - 16 * MvPolynomial.X 1 + 1) ^ 3)
        = (256 * lambdaNModC (AlgebraicClosure ℚ) q ^ 2 - 16 * lambdaNModC (AlgebraicClosure ℚ) q + 1) ^ 3 := by
      simp only [map_pow, map_add, map_sub, map_mul, map_ofNat, map_one, lambdaEval_X1]
    have hD0' : lambdaNModC (AlgebraicClosure ℚ) q ^ 2 * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) ^ 2 ≠ 0 :=
      hD ▸ hD0
    rw [Subring.coe_mul, coe_E, hN, eq_inv_of_mul_eq_one_left hinv, hD]
    exact ((eq_mul_inv_iff_mul_eq₀ hD0').mpr (by rw [← mul_assoc]; exact jLambda_Qb_q q)).symm
  · exact h
  · exact h'

end S_ModularCurve_LambdaNodeLocalized_exists_qExpand_two_jq_sub_eq_unit_mul_pow_jWidth_of_eq_zero_or_eq_1728
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_qExpand_two_jq_sub_eq_unit_mul_pow_jWidth_of_eq_zero_or_eq_1728 (solution)
