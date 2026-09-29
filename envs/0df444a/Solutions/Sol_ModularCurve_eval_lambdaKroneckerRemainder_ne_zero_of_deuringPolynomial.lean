-- Prove2me | solution 1 for ModularCurve.eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7a7a811c-0f5c-5ec2-846a-570cede21661

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_Polynomial_DeuringPolynomial
import Theorems.Thm_ModularCurve_lambdaKroneckerRemainder_frobeniusGraph_ode
import Theorems.Thm_Polynomial_eval_zero_deuringPolynomial_map
import Theorems.Thm_Polynomial_eval_one_deuringPolynomial_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.jqNModC_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
set_option autoImplicit false

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "LambdaModularPolynomialData lambdaKroneckerRemainder_frobeniusGraph_ode"
namespace L10
p2m_open "ModularCurve"

theorem eval_map_eval_X_pow {k : Type*} [CommRing k] (R : Polynomial (Polynomial ℤ)) (q : ℕ) (a : k) :
    ((R.eval (X ^ q)).map (Int.castRingHom k)).eval a =
      ((R.map (mapRingHom (Int.castRingHom k))).eval (C (a ^ q))).eval a := by
  set ψ : Polynomial ℤ →+* k := eval₂RingHom (Int.castRingHom k) a with hψ
  have h1 : ((R.eval (X ^ q)).map (Int.castRingHom k)).eval a = R.eval₂ ψ (a ^ q) := by
    rw [eval_map]
    have h := Polynomial.hom_eval₂ R (RingHom.id _) ψ (X ^ q)
    rw [RingHom.comp_id, map_pow] at h
    have hX : ψ X = a := by simp [hψ]
    rw [hX] at h
    rw [← h]
    rfl
  have h2 : ((R.map (mapRingHom (Int.castRingHom k))).eval (C (a ^ q))).eval a
      = R.eval₂ ψ (a ^ q) := by
    rw [eval_map, ← coe_evalRingHom, Polynomial.hom_eval₂, coe_evalRingHom, eval_C]
    congr 1
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp [hψ]
    · simp [hψ]
  rw [h1, h2]

theorem sq_dvd_wronskian {k : Type*} [Field k] {P Q : Polynomial k} {a : k}
    (hP : P.IsRoot a) (hQ : Q.IsRoot a) :
    (X - C a) ^ 2 ∣ derivative P * Q - P * derivative Q := by
  obtain ⟨P₁, rfl⟩ := dvd_iff_isRoot.mpr hP
  obtain ⟨Q₁, rfl⟩ := dvd_iff_isRoot.mpr hQ
  refine ⟨derivative P₁ * Q₁ - P₁ * derivative Q₁, ?_⟩
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  ring

theorem main_deuring {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (data : LambdaModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    {k : Type*} [Field k] [CharP k q]
    (l : k) (hl : ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)).eval (16 * l) = 0) :
    ((R.map (mapRingHom (Int.castRingHom k))).eval (C (l ^ q))).eval l ≠ 0 := by
  have hp : q.Prime := Fact.out
  set G : Polynomial k := (R.eval (X ^ q)).map (Int.castRingHom k) with hG
  set F : Polynomial k := X ^ (q ^ 2) - X with hF
  set H : Polynomial k := ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)).comp (16 * X) with hH
  have hODE : (derivative G * F - G * derivative F) * H ^ 2 =
      (X ^ (q - 1) * H ^ 2 - (X * (1 - 16 * X)) ^ (q - 1)) * F ^ 2 :=
    lambdaKroneckerRemainder_frobeniusGraph_ode q hq data R hR k
  have hF' : derivative F = -1 := by
    rw [hF, derivative_sub, derivative_X_pow, derivative_X, Nat.cast_pow, CharP.cast_eq_zero k q,
      zero_pow two_ne_zero, C_0, zero_mul, zero_sub]
  have hHl : H.IsRoot l := by
    rw [IsRoot, hH, eval_comp, eval_mul, eval_X]
    simpa using hl

  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero, Polynomial.eval_zero_deuringPolynomial_map] at hl
    exact one_ne_zero hl
  have hl1 : 1 - 16 * l ≠ 0 := by
    intro h
    have h16 : 16 * l = 1 := by linear_combination -h
    rw [h16, Polynomial.eval_one_deuringPolynomial_map] at hl
    exact (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hl
  have hcof : (l * (1 - 16 * l)) ^ (q - 1) ≠ 0 := pow_ne_zero _ (mul_ne_zero hl0 hl1)

  have hFl : F.IsRoot l := by
    have h := congrArg (fun P : Polynomial k => P.eval l) hODE
    have hH0 : H.eval l = 0 := hHl
    simp only [eval_mul, eval_sub, eval_pow, eval_X, hH0, eval_one, eval_ofNat, zero_pow two_ne_zero, mul_zero,
      zero_sub] at h

    have h2 : (l * (1 - 16 * l)) ^ (q - 1) * (F.eval l) ^ 2 = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hcof
    · exact (pow_eq_zero_iff two_ne_zero).mp h3

  intro hGl0
  have hGl : G.IsRoot l := by rw [IsRoot, hG, eval_map_eval_X_pow]; exact hGl0
  have hL : (X - C l) ^ 3 ∣ (derivative G * F - G * derivative F) * H ^ 2 := by
    have h1 : (X - C l) ^ 2 ∣ derivative G * F - G * derivative F := sq_dvd_wronskian hGl hFl
    have h2 : (X - C l) ∣ H := dvd_iff_isRoot.mpr hHl
    calc (X - C l) ^ 3 = (X - C l) ^ 2 * (X - C l) := by ring
      _ ∣ (derivative G * F - G * derivative F) * H := mul_dvd_mul h1 h2
      _ ∣ (derivative G * F - G * derivative F) * H ^ 2 := by
        rw [sq, ← mul_assoc]; exact dvd_mul_right _ _
  have hRt : ¬ (X - C l) ^ 3 ∣ (X ^ (q - 1) * H ^ 2 - (X * (1 - 16 * X)) ^ (q - 1)) * F ^ 2 := by
    obtain ⟨F₁, hF₁⟩ := dvd_iff_isRoot.mpr hFl
    have hF₁l : F₁.eval l ≠ 0 := by
      have h := congrArg (fun P => (derivative P).eval l) hF₁
      simp only [hF', derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
        eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_neg,
        eval_one] at h
      rw [← h]; norm_num
    set P : Polynomial k := X ^ (q - 1) * H ^ 2 - (X * (1 - 16 * X)) ^ (q - 1) with hP
    have hPl : P.eval l ≠ 0 := by
      have hH0 : H.eval l = 0 := hHl
      simp only [hP, eval_sub, eval_mul, eval_pow, eval_X, hH0, eval_one, eval_ofNat]
      rw [zero_pow two_ne_zero, mul_zero, zero_sub, neg_ne_zero]
      exact hcof
    intro hdvd
    rw [hF₁] at hdvd
    have h3 : (X - C l) ^ 3 = (X - C l) ^ 2 * (X - C l) := by ring
    have h4 : P * ((X - C l) * F₁) ^ 2 = (X - C l) ^ 2 * (P * F₁ ^ 2) := by ring
    rw [h3, h4, mul_dvd_mul_iff_left (pow_ne_zero 2 (X_sub_C_ne_zero l))] at hdvd
    have h5 : (P * F₁ ^ 2).IsRoot l := dvd_iff_isRoot.mp hdvd
    rw [IsRoot, eval_mul, eval_pow] at h5
    exact mul_ne_zero hPl (pow_ne_zero 2 hF₁l) h5
  exact hRt (hODE ▸ hL)

end ModularCurve.L10

open Polynomial in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (data : LambdaModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    {k : Type*} [Field k] [CharP k q]
    (l : k) (hl : ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)).eval (16 * l) = 0) :
    ((R.map (mapRingHom (Int.castRingHom k))).eval (C (l ^ q))).eval l ≠ 0 :=
  ModularCurve.L10.main_deuring hq data R hR l hl

end S_ModularCurve_eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial
end P2MW
export P2MW.S_ModularCurve_eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial (solution)
