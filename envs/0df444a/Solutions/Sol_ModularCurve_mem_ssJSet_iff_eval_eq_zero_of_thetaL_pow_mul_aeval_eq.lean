-- Prove2me | solution 1 for ModularCurve.mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/57e80127-f8ca-52bc-94d6-92dfb2573823

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace SSBridge

open ModularCurve Polynomial

section Arith

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (Ω : Type) [Field Ω] [CharP Ω p]
include hp5

theorem not_dvd_of_lt_five {n : ℕ} (hn : n ∣ 2 ^ 6 * 3 ^ 3) (hpn : p ∣ n) : False := by
  have hp : p.Prime := Fact.out
  have h := dvd_trans hpn hn
  rcases (Nat.Prime.prime hp).dvd_or_dvd h with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega

theorem cast1728_ne_zero : (1728 : Ω) ≠ 0 := by
  intro h
  have h' : ((1728 : ℕ) : Ω) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff Ω p] at h'
  exact not_dvd_of_lt_five p hp5 (n := 1728) (by norm_num) h'

theorem two_ne_zero' : (2 : Ω) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : Ω) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff Ω p] at h'
  exact not_dvd_of_lt_five p hp5 (n := 2) (by norm_num) h'

theorem one_ne_neg_one : (1 : Ω) ≠ -1 := by
  intro h
  apply two_ne_zero' p hp5 Ω
  linear_combination h

end Arith

section Main

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [DecidableEq Ω]

theorem eval_eq_zero_iff (T : Finset Ω) (e₄ e₆ : ℕ) (he₄ : e₄ ≤ 1) (he₆ : e₆ ≤ 1) (j₀ : Ω) :
    Polynomial.eval j₀ (X ^ e₄ * (X - C (1728 : Ω)) ^ e₆ * ∏ a ∈ T, (X - C a)) = 0 ↔
      (e₄ = 1 ∧ j₀ = 0) ∨ (e₆ = 1 ∧ j₀ = 1728) ∨ j₀ ∈ T := by
  rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_prod, eval_sub, eval_X, eval_C]
  simp only [eval_sub, eval_X, eval_C, mul_eq_zero, Finset.prod_eq_zero_iff, sub_eq_zero,
    exists_eq_right']
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he₄ with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he₆ with rfl | rfl <;> simp [sub_eq_zero, or_assoc]

include hp5 in
theorem main (m e₄ e₆ : ℕ) (S : Polynomial Ω)
    (hS : 12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      S.Monic ∧ S.Separable ∧ S.natDegree = m ∧ S.eval 0 ≠ 0 ∧ S.eval 1728 ≠ 0 ∧
      thetaL Ω (jqModC Ω) ^ ((p - 1) / 2) * Polynomial.aeval (jqModC Ω) S =
        (-1) ^ ((p - 1) / 2) *
          (jqModC Ω ^ (4 * m + e₄ + 2 * e₆) * (jqModC Ω - 1728) ^ (3 * m + e₄ + e₆)))
    (j₀ : Ω) :
    j₀ ∈ ModularCurve.ssJSet p Ω ↔ Polynomial.eval j₀ (X ^ e₄ * (X - C (1728 : Ω)) ^ e₆ * S) = 0 := by
  classical
  obtain ⟨hm, he₄, he₆, hmonic, -, -, -, -, hid⟩ := hS

  set S₀ : Finset Ω := (ssJSet_finite p Ω).toFinset with hS₀def
  have hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet p Ω := fun a => Set.Finite.mem_toFinset _
  set T : Finset Ω := S₀ \ {0, 1728} with hT
  set Sss : Polynomial Ω := ∏ a ∈ T, (X - C a) with hSss
  set J := jqModC Ω with hJ
  have htr : Transcendental Ω J := transcendental_jqModC Ω

  have hsq := ModularCurve.thetaL_jqModC_pow_mul_prod_sq_eq p hp5 m e₄ e₆ hm (he₄.trans one_le_two) he₆
    Ω S₀ hS₀
  rw [← hJ, ← hT] at hsq
  have haevalSss : Polynomial.aeval J Sss = ∏ a ∈ T, (J - HahnSeries.C a) := by
    rw [hSss, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_sub, aeval_X, aeval_C]
    congr 1
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HahnSeries.ofPowerSeries_C]

  have hJne : ∀ c : Ω, J ≠ algebraMap Ω (LaurentSeries Ω) c := by
    intro c h; exact htr (h ▸ isAlgebraic_algebraMap c)
  have hJ0 : J ≠ 0 := by simpa using hJne 0
  have hJ1728 : J - 1728 ≠ 0 := by
    rw [sub_ne_zero]
    have := hJne 1728
    rwa [map_ofNat] at this
  have hRHS : J ^ (8 * m + 2 * e₄ + 4 * e₆) * (J - 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ1728)
  have hθ : thetaL Ω J ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by have := hp5; omega), zero_mul] at hsq
    exact hRHS hsq.symm

  have hk : (p - 1) / 2 * 2 = p - 1 := by omega
  have hid2 : thetaL Ω J ^ (p - 1) * (Polynomial.aeval J S) ^ 2 =
      J ^ (8 * m + 2 * e₄ + 4 * e₆) * (J - 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) := by
    have h := congrArg (fun x => x ^ 2) hid
    beta_reduce at h
    rw [mul_pow, ← pow_mul, hk, mul_pow, ← pow_mul, mul_comm ((p - 1) / 2) 2, pow_mul, neg_one_sq,
      one_pow, one_mul, mul_pow, ← pow_mul, ← pow_mul] at h
    rw [h]
    congr 1 <;> congr 1 <;> ring

  have hsq' : (Polynomial.aeval J S) ^ 2 = (Polynomial.aeval J Sss) ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero (p - 1) hθ)
    rw [hid2, haevalSss, hsq]

  have hinj : Function.Injective (Polynomial.aeval J : Polynomial Ω →ₐ[Ω] LaurentSeries Ω) :=
    transcendental_iff_injective.mp htr
  have hSssMonic : Sss.Monic := monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a
  have hSeq : S = Sss := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with h | h
    · exact hinj h
    · exfalso
      have h' : S = -Sss := hinj (by rw [map_neg]; exact h)
      have hl := congrArg Polynomial.leadingCoeff h'
      rw [leadingCoeff_neg, hmonic.leadingCoeff, hSssMonic.leadingCoeff] at hl
      exact one_ne_neg_one p hp5 Ω hl

  have h1728ne : (1728 : Ω) ≠ 0 := cast1728_ne_zero p hp5 Ω
  have he₄iff : e₄ = 1 ↔ (0 : Ω) ∈ ssJSet p Ω := by
    rw [ModularCurve.zero_mem_ssJSet_iff p hp5 Ω]; omega
  have he₆iff : e₆ = 1 ↔ (1728 : Ω) ∈ ssJSet p Ω := by
    rw [ModularCurve.ofNat1728_mem_ssJSet_iff p hp5 Ω]; omega
  have hTmem : j₀ ∈ T ↔ j₀ ∈ ssJSet p Ω ∧ j₀ ≠ 0 ∧ j₀ ≠ 1728 := by
    rw [hT, Finset.mem_sdiff, hS₀, Finset.mem_insert, Finset.mem_singleton, not_or]
  rw [hSeq, hSss, eval_eq_zero_iff Ω T e₄ e₆ he₄ he₆ j₀, hTmem, he₄iff, he₆iff]
  by_cases h0 : j₀ = 0
  · subst h0
    simp [h1728ne.symm]
  · by_cases h1 : j₀ = 1728
    · subst h1
      simp [h1728ne]
    · simp [h0, h1]

end Main

end SSBridge

end

open ModularCurve Polynomial in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (m e₄ e₆ : ℕ) (S : Polynomial Ω)
    (hS : 12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      S.Monic ∧ S.Separable ∧ S.natDegree = m ∧ S.eval 0 ≠ 0 ∧ S.eval 1728 ≠ 0 ∧
      thetaL Ω (jqModC Ω) ^ ((p - 1) / 2) * Polynomial.aeval (jqModC Ω) S =
        (-1) ^ ((p - 1) / 2) *
          (jqModC Ω ^ (4 * m + e₄ + 2 * e₆) * (jqModC Ω - 1728) ^ (3 * m + e₄ + e₆)))
    (j₀ : Ω) :
    j₀ ∈ ModularCurve.ssJSet p Ω ↔ Polynomial.eval j₀ (X ^ e₄ * (X - C (1728 : Ω)) ^ e₆ * S) = 0 :=
  SSBridge.main p hp5 Ω m e₄ e₆ S hS j₀

#print axioms solution

end S_ModularCurve_mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq
end P2MW
export P2MW.S_ModularCurve_mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq (solution)
