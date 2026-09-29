-- Prove2me | solution 1 for ModularCurve.eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7df8b9aa-6155-5d9b-9a25-2222c41a84bb

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_kroneckerRemainder_frobeniusGraph_ode
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_ssJSet_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.jqNModC_one ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData ssJSet kroneckerRemainder_frobeniusGraph_ode pow_q_sq_eq_self_of_mem_ssJSet ssJSet_finite"
namespace K2main
p2m_open "ModularCurve"

theorem exists_weight_decomp (q : ℕ) (hp : q.Prime) (hq : 5 ≤ q) :
    ∃ m e₄ e₆ : ℕ, 12 * m + 4 * e₄ + 6 * e₆ = q - 1 ∧ e₄ ≤ 2 ∧ e₆ ≤ 1 := by
  have h2 : ¬ 2 ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h; omega
  have h3 : ¬ 3 ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
  refine ⟨(q - 1) / 12, if (q - 1) % 12 = 4 ∨ (q - 1) % 12 = 10 then 1 else 0,
    if (q - 1) % 12 = 6 ∨ (q - 1) % 12 = 10 then 1 else 0, ?_, ?_, ?_⟩
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega

theorem sq_dvd_wronskian {k : Type*} [Field k] {P Q : Polynomial k} {a : k}
    (hP : P.IsRoot a) (hQ : Q.IsRoot a) :
    (X - C a) ^ 2 ∣ derivative P * Q - P * derivative Q := by
  obtain ⟨P₁, rfl⟩ := dvd_iff_isRoot.mpr hP
  obtain ⟨Q₁, rfl⟩ := dvd_iff_isRoot.mpr hQ
  refine ⟨derivative P₁ * Q₁ - P₁ * derivative Q₁, ?_⟩
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  ring

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

theorem main {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (data : ModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet q k) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    ((R.map (mapRingHom (Int.castRingHom k))).eval (C (a ^ q))).eval a ≠ 0 := by
  have hp : q.Prime := Fact.out
  obtain ⟨m, e₄, e₆, hm, he₄, he₆⟩ := exists_weight_decomp q hp hq

  set S₀ : Finset k := (ssJSet_finite q k).toFinset with hS₀def
  have hS₀ : ∀ b, b ∈ S₀ ↔ b ∈ ssJSet q k := fun b => by rw [hS₀def, Set.Finite.mem_toFinset]

  set G : Polynomial k := (R.eval (X ^ q)).map (Int.castRingHom k) with hG
  set F : Polynomial k := X ^ (q ^ 2) - X with hF
  set s : Polynomial k := ∏ b ∈ S₀ \ {0, 1728}, (X - C b) with hs
  have hODE : (derivative G * F - G * derivative F) * s ^ 2 =
      (X ^ (q - 1) * s ^ 2 - X ^ (8 * m + 2 * e₄ + 4 * e₆) * (X - C 1728) ^ (6 * m + 2 * e₄ + 2 * e₆)) * F ^ 2 :=
    kroneckerRemainder_frobeniusGraph_ode q hq data R hR m e₄ e₆ hm he₄ he₆ k S₀ hS₀

  have hFa : F.IsRoot a := by
    rw [IsRoot, hF, eval_sub, eval_pow, eval_X, pow_q_sq_eq_self_of_mem_ssJSet q ha, sub_self]
  have hF' : derivative F = -1 := by
    rw [hF, derivative_sub, derivative_X_pow, derivative_X, Nat.cast_pow, CharP.cast_eq_zero k q,
      zero_pow two_ne_zero, C_0, zero_mul, zero_sub]
  have has : a ∈ S₀ \ {0, 1728} := by
    rw [Finset.mem_sdiff, hS₀]
    exact ⟨ha, by simp [h0, h1728]⟩
  have hsa : s.IsRoot a := by
    rw [IsRoot, hs, eval_prod]
    exact Finset.prod_eq_zero has (by simp)

  intro hGa0
  have hGa : G.IsRoot a := by rw [IsRoot, hG, eval_map_eval_X_pow]; exact hGa0

  have hL : (X - C a) ^ 3 ∣ (derivative G * F - G * derivative F) * s ^ 2 := by
    have h1 : (X - C a) ^ 2 ∣ derivative G * F - G * derivative F := sq_dvd_wronskian hGa hFa
    have h2 : (X - C a) ∣ s := dvd_iff_isRoot.mpr hsa
    calc (X - C a) ^ 3 = (X - C a) ^ 2 * (X - C a) := by ring
      _ ∣ (derivative G * F - G * derivative F) * s := mul_dvd_mul h1 h2
      _ ∣ (derivative G * F - G * derivative F) * s ^ 2 := by
        rw [sq, ← mul_assoc]; exact dvd_mul_right _ _

  have hR : ¬ (X - C a) ^ 3 ∣
      (X ^ (q - 1) * s ^ 2 - X ^ (8 * m + 2 * e₄ + 4 * e₆) * (X - C 1728) ^ (6 * m + 2 * e₄ + 2 * e₆)) * F ^ 2 := by
    obtain ⟨F₁, hF₁⟩ := dvd_iff_isRoot.mpr hFa
    have hF₁a : F₁.eval a ≠ 0 := by
      have h := congrArg (fun P => (derivative P).eval a) hF₁
      simp only [hF', derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
        eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_neg,
        eval_one] at h
      rw [← h]; norm_num
    set P : Polynomial k := X ^ (q - 1) * s ^ 2
      - X ^ (8 * m + 2 * e₄ + 4 * e₆) * (X - C 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) with hP
    have hPa : P.eval a ≠ 0 := by
      have hs0 : s.eval a = 0 := hsa
      simp only [hP, eval_sub, eval_mul, eval_pow, eval_X, hs0, eval_C]
      rw [zero_pow two_ne_zero, mul_zero, zero_sub, neg_ne_zero]
      exact mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ (sub_ne_zero.mpr h1728))
    intro hdvd
    rw [hF₁] at hdvd
    have h3 : (X - C a) ^ 3 = (X - C a) ^ 2 * (X - C a) := by ring
    have h4 : P * ((X - C a) * F₁) ^ 2 = (X - C a) ^ 2 * (P * F₁ ^ 2) := by ring
    rw [h3, h4, mul_dvd_mul_iff_left (pow_ne_zero 2 (X_sub_C_ne_zero a))] at hdvd
    have h5 : (P * F₁ ^ 2).IsRoot a := dvd_iff_isRoot.mp hdvd
    rw [IsRoot, eval_mul, eval_pow] at h5
    exact mul_ne_zero hPa (pow_ne_zero 2 hF₁a) h5
  exact hR (hODE ▸ hL)

end ModularCurve.K2main

open Polynomial in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (data : ModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet q k) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    ((R.map (mapRingHom (Int.castRingHom k))).eval (C (a ^ q))).eval a ≠ 0 :=
  ModularCurve.K2main.main hq data R hR a ha h0 h1728

end S_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet (solution)
