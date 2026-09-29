-- Prove2me | solution 1 for ModularCurve.lambdaKroneckerRemainder_frobeniusGraph_ode
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/83411807-dfb3-5066-9ee7-9696df7f1c6b

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_Polynomial_DeuringPolynomial
import Theorems.Thm_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul
import Theorems.Thm_ModularCurve_laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow
import Theorems.Thm_ModularCurve_thetaL_laurentMap_lambdaDworkQuotient
import Theorems.Thm_ModularCurve_deuringPolynomial_sq_mul_thetaL_lambda_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_lambdaKroneckerRemainder_frobeniusGraph_ode
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.jqNModC_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false

p2m_open "HahnSeries Polynomial ModularCurve P2MW.S_ModularCurve_lambdaKroneckerRemainder_frobeniusGraph_ode.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "lambdaInt lambdaModC evalAtLambdaInt qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd etaProd constantCoeff_etaProd dedekindEtaUnitInv laurentMap laurentMap_coeff LambdaModularPolynomialData thetaL thetaL_apply existsUnique_qExpand_sub_pow_eq_natCast_mul laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow thetaL_laurentMap_lambdaDworkQuotient deuringPolynomial_sq_mul_thetaL_lambda_pow"
namespace L9
p2m_open "ModularCurve"

section ThetaR

variable {R : Type*} [CommRing R]

noncomputable def thetaR (f : LaurentSeries R) : LaurentSeries R :=
  single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f

theorem coeff_single_one_mul_derivative_add_one (f : LaurentSeries R) (m : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff (m + 1) =
      ((m + 1 : ℤ) : R) * f.coeff (m + 1) := by
  rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, zsmul_eq_mul]
  simp only [Nat.cast_one]

theorem coeff_single_one_mul_derivative (f : LaurentSeries R) (n : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff n = (n : R) * f.coeff n := by
  have h := coeff_single_one_mul_derivative_add_one f (n - 1)
  simp only [sub_add_cancel] at h
  exact h

theorem coeff_thetaR (f : LaurentSeries R) (n : ℤ) : (thetaR f).coeff n = (n : R) * f.coeff n :=
  coeff_single_one_mul_derivative f n

theorem thetaR_add (f g : LaurentSeries R) : thetaR (f + g) = thetaR f + thetaR g := by
  ext n; simp [coeff_thetaR, mul_add]

theorem thetaR_sub (f g : LaurentSeries R) : thetaR (f - g) = thetaR f - thetaR g := by
  ext n; simp [coeff_thetaR, mul_sub]

theorem thetaR_natCast_mul (m : ℕ) (f : LaurentSeries R) :
    thetaR ((m : LaurentSeries R) * f) = (m : LaurentSeries R) * thetaR f := by
  ext n
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := R)) m, HahnSeries.C_mul_eq_smul,
    HahnSeries.C_mul_eq_smul, coeff_thetaR, HahnSeries.coeff_smul, HahnSeries.coeff_smul,
    coeff_thetaR, smul_eq_mul, smul_eq_mul]
  ring

theorem support_thetaR_subset (f : LaurentSeries R) : (thetaR f).support ⊆ f.support := by
  intro n hn
  rw [HahnSeries.mem_support, coeff_thetaR] at hn
  rw [HahnSeries.mem_support]
  exact right_ne_zero_of_mul hn

theorem thetaR_mul (f g : LaurentSeries R) : thetaR (f * g) = thetaR f * g + f * thetaR g := by
  ext n
  rw [HahnSeries.coeff_add, coeff_thetaR, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_left' f.isPWO_support (support_thetaR_subset f),
    HahnSeries.coeff_mul_right' g.isPWO_support (support_thetaR_subset g),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, hsum⟩ := hij
  rw [coeff_thetaR, coeff_thetaR, ← hsum, Int.cast_add]
  ring

theorem thetaR_pow (f : LaurentSeries R) (m : ℕ) :
    thetaR (f ^ (m + 1)) = ((m + 1 : ℕ) : LaurentSeries R) * (f ^ m * thetaR f) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, thetaR_mul, ih]
    push_cast
    ring

theorem thetaR_qExpand (N : ℕ) [NeZero N] (f : LaurentSeries R) :
    thetaR (qExpand R N f) = (N : LaurentSeries R) * qExpand R N (thetaR f) := by
  ext n
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := R)) N, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, smul_eq_mul, coeff_thetaR]
  by_cases hn : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeff_thetaR, Int.cast_mul, Int.cast_natCast]
    ring
  · rw [qExpand_coeff_of_not_dvd N _ hn, qExpand_coeff_of_not_dvd N _ hn, mul_zero, mul_zero]

theorem laurentMap_thetaR {k : Type*} [Field k] (φ : R →+* k) (f : LaurentSeries R) :
    laurentMap φ (thetaR f) = thetaL k (laurentMap φ f) := by
  ext n
  rw [thetaL_apply, coeff_single_one_mul_derivative, laurentMap_coeff, coeff_thetaR, map_mul,
    map_intCast, laurentMap_coeff]

end ThetaR

section OverField

variable {k : Type*} [Field k]

theorem thetaL_eq_thetaR (f : LaurentSeries k) : thetaL k f = thetaR f := rfl

theorem thetaR_C' (a : k) : thetaR (HahnSeries.C a : LaurentSeries k) = 0 := by
  ext n
  rw [coeff_thetaR, HahnSeries.coeff_zero]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn, mul_zero]

theorem thetaR_pow' (f : LaurentSeries k) (n : ℕ) :
    thetaR (f ^ n) = (n : LaurentSeries k) * (f ^ (n - 1) * thetaR f) := by
  cases n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, ← HahnSeries.C_one]
    exact thetaR_C' 1
  | succ m => rw [thetaR_pow, Nat.add_sub_cancel]

theorem thetaL_aeval (J : LaurentSeries k) (P : Polynomial k) :
    thetaL k (aeval J P) = aeval J (derivative P) * thetaL k J := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, hp, hq]
  | monomial n a =>
    rw [derivative_monomial, aeval_monomial, aeval_monomial, LaurentSeries.algebraMap_apply,
      LaurentSeries.algebraMap_apply, thetaL_eq_thetaR, thetaL_eq_thetaR, thetaR_mul, thetaR_C', zero_mul,
      zero_add, thetaR_pow', map_mul, map_natCast]
    ring

end OverField

section OrderLC

variable {k : Type*} [Field k]

theorem order_mul' {f g : LaurentSeries k} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).order = f.order + g.order :=
  HahnSeries.order_mul_of_ne_zero (mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hf)
    (HahnSeries.leadingCoeff_ne_zero.mpr hg))

theorem leadingCoeff_mul' {f g : LaurentSeries k} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).leadingCoeff = f.leadingCoeff * g.leadingCoeff :=
  HahnSeries.leadingCoeff_mul_of_ne_zero (mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hf)
    (HahnSeries.leadingCoeff_ne_zero.mpr hg))

theorem order_pow' {f : LaurentSeries k} (hf : f ≠ 0) (n : ℕ) : (f ^ n).order = n • f.order := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, order_mul' (pow_ne_zero n hf) hf, ih, succ_nsmul]

theorem leadingCoeff_pow' {f : LaurentSeries k} (hf : f ≠ 0) (n : ℕ) :
    (f ^ n).leadingCoeff = f.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, leadingCoeff_mul' (pow_ne_zero n hf) hf, ih, pow_succ]

theorem order_prod' {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries k) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).order = ∑ i ∈ s, (f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      order_mul' (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem leadingCoeff_prod' {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries k) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).leadingCoeff = ∏ i ∈ s, (f i).leadingCoeff := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      leadingCoeff_mul' (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem order_eq_of_coeff {f : LaurentSeries k} {g : ℤ} (hg : f.coeff g ≠ 0)
    (hlt : ∀ n < g, f.coeff n = 0) : f.order = g := by
  have hne : f ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hg
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hg) ?_
  by_contra h
  rw [not_le] at h
  exact hne (HahnSeries.coeff_order_eq_zero.mp (hlt _ h))

theorem leadingCoeff_eq_of_coeff {f : LaurentSeries k} {g : ℤ} (hg : f.coeff g ≠ 0)
    (hlt : ∀ n < g, f.coeff n = 0) : f.leadingCoeff = f.coeff g := by
  rw [HahnSeries.leadingCoeff_eq, order_eq_of_coeff hg hlt]

end OrderLC

section LambdaNorm

def IsOneUnit {R : Type*} [CommRing R] (x : LaurentSeries R) : Prop := x.coeff 0 = 1 ∧ ∀ n < 0, x.coeff n = 0

namespace IsOneUnit

variable {R : Type*} [CommRing R]

theorem ofPowerSeries (P : PowerSeries R) (hP : PowerSeries.constantCoeff P = 1) :
    IsOneUnit (HahnSeries.ofPowerSeries ℤ R P) := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [PowerSeries.coeff_coe, if_neg (by omega)]; simpa using hP
  · rw [PowerSeries.coeff_coe, if_pos hn]

theorem mul {x y : LaurentSeries R} (hx : IsOneUnit x) (hy : IsOneUnit y) : IsOneUnit (x * y) := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [HahnSeries.coeff_mul, Finset.sum_eq_single ((0, 0) : ℤ × ℤ)]
    · rw [hx.1, hy.1, mul_one]
    · intro ij hij hne
      rw [Finset.mem_antidiagonal] at hij
      obtain ⟨h1, h2, h3⟩ := hij
      have hi : 0 ≤ ij.1 := by
        by_contra h; rw [not_le] at h; exact (HahnSeries.mem_support _ _).mp h1 (hx.2 _ h)
      have hj : 0 ≤ ij.2 := by
        by_contra h; rw [not_le] at h; exact (HahnSeries.mem_support _ _).mp h2 (hy.2 _ h)
      exfalso; apply hne
      exact Prod.ext (by omega) (by omega)
    · intro h
      rw [Finset.mem_antidiagonal, not_and_or, not_and_or] at h
      rcases h with h | h | h
      · rw [HahnSeries.mem_support, not_not] at h; rw [h, zero_mul]
      · rw [HahnSeries.mem_support, not_not] at h; rw [h, mul_zero]
      · exact absurd (by simp) h
  · rw [HahnSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    exfalso
    by_cases hi : ij.1 < 0
    · exact (HahnSeries.mem_support _ _).mp h1 (hx.2 _ hi)
    · exact (HahnSeries.mem_support _ _).mp h2 (hy.2 _ (by omega))

theorem pow {x : LaurentSeries R} (hx : IsOneUnit x) (n : ℕ) : IsOneUnit (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact ⟨by simp, fun n hn => by rw [HahnSeries.coeff_one, if_neg hn.ne]⟩
  | succ n ih => rw [pow_succ]; exact ih.mul hx

theorem qExpand {x : LaurentSeries R} (hx : IsOneUnit x) (N : ℕ) [NeZero N] : IsOneUnit (ModularCurve.qExpand R N x) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have h := qExpand_coeff_mul (R := R) N x 0
    rw [mul_zero] at h
    rw [h, hx.1]
  · by_cases hd : (N : ℤ) ∣ n
    · obtain ⟨c, rfl⟩ := hd
      rw [qExpand_coeff_mul]
      have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      exact hx.2 c (by nlinarith)
    · exact qExpand_coeff_of_not_dvd N x hd

end IsOneUnit

theorem lambdaInt_eq : lambdaInt = HahnSeries.single (1 : ℤ) (1 : ℤ) *
    (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 * ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)) := by
  rw [lambdaInt]; ring

theorem isOneUnit_lambdaInt_tail : IsOneUnit
    (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 * ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)) := by
  have hE : IsOneUnit (HahnSeries.ofPowerSeries ℤ ℤ etaProd) := IsOneUnit.ofPowerSeries _ constantCoeff_etaProd
  have hD : IsOneUnit (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) := by
    refine IsOneUnit.ofPowerSeries _ ?_
    rw [dedekindEtaUnitInv, PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
  exact ((hE.pow 8).mul ((hE.pow 16).qExpand 4)).mul (hD.qExpand 2)

theorem coeff_lambdaInt_one : lambdaInt.coeff 1 = 1 := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : ℤ))
    (x := HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 * ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)) (a := 0) (b := (1 : ℤ))
  rw [zero_add, one_mul] at h
  rw [lambdaInt_eq, h]
  exact isOneUnit_lambdaInt_tail.1

theorem coeff_lambdaInt_of_lt {n : ℤ} (hn : n < 1) : lambdaInt.coeff n = 0 := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : ℤ))
    (x := HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 * ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)) (a := n - 1) (b := (1 : ℤ))
  rw [sub_add_cancel, one_mul] at h
  rw [lambdaInt_eq, h]
  exact isOneUnit_lambdaInt_tail.2 _ (by omega)

variable {k : Type*} [Field k]

theorem coeff_lambdaModC_one : (lambdaModC k).coeff 1 = 1 := by
  rw [lambdaModC, laurentMap_coeff, coeff_lambdaInt_one, map_one]

theorem coeff_lambdaModC_of_lt {n : ℤ} (hn : n < 1) : (lambdaModC k).coeff n = 0 := by
  rw [lambdaModC, laurentMap_coeff, coeff_lambdaInt_of_lt hn, map_zero]

theorem lambdaModC_ne_zero : lambdaModC k ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero (by rw [coeff_lambdaModC_one]; exact one_ne_zero)

theorem order_lambdaModC : (lambdaModC k).order = 1 :=
  order_eq_of_coeff (by rw [coeff_lambdaModC_one]; exact one_ne_zero) fun n hn => coeff_lambdaModC_of_lt hn

theorem leadingCoeff_lambdaModC : (lambdaModC k).leadingCoeff = 1 := by
  rw [leadingCoeff_eq_of_coeff (by rw [coeff_lambdaModC_one]; exact one_ne_zero) fun n hn => coeff_lambdaModC_of_lt hn,
    coeff_lambdaModC_one]

theorem aeval_lambdaModC_injective : Function.Injective (aeval (lambdaModC k) : Polynomial k →ₐ[k] LaurentSeries k) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  by_contra hne
  set d := P.natTrailingDegree with hd
  have hcd : P.coeff d ≠ 0 := by
    rw [hd]; exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hne
  have h := congrArg (fun x : LaurentSeries k => x.coeff (d : ℤ)) hP
  simp only [HahnSeries.coeff_zero] at h
  rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum] at h
  simp only [Algebra.smul_def, LaurentSeries.algebraMap_apply] at h
  have hord : ∀ i : ℕ, ((lambdaModC k) ^ i).order = i := fun i => by
    rw [order_pow' lambdaModC_ne_zero, order_lambdaModC]; simp
  rw [Finset.sum_eq_single d] at h
  · rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] at h
    have hpow : ((lambdaModC k) ^ d).coeff (d : ℤ) = 1 := by
      have hl : ((lambdaModC k) ^ d).leadingCoeff = 1 := by
        rw [leadingCoeff_pow' lambdaModC_ne_zero, leadingCoeff_lambdaModC, one_pow]
      rw [HahnSeries.leadingCoeff_eq, hord] at hl
      exact hl
    rw [hpow, mul_one] at h
    exact hcd h
  · intro i _ hid
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    rcases lt_or_gt_of_ne hid with hlt | hgt
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hd ▸ hlt), zero_mul]
    · rw [HahnSeries.coeff_eq_zero_of_lt_order (by rw [hord]; exact_mod_cast hgt), mul_zero]
  · intro h'
    exfalso; apply h'
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hd ▸ Polynomial.natTrailingDegree_le_natDegree P)

end LambdaNorm

theorem laurentMap_evalAtLambdaInt (k : Type*) [Field k] (P : Polynomial ℤ) :
    laurentMap (Int.castRingHom k) (evalAtLambdaInt P) = aeval (lambdaModC k) (P.map (Int.castRingHom k)) := by
  have h : (laurentMap (Int.castRingHom k)).comp evalAtLambdaInt =
      (aeval (lambdaModC k)).toRingHom.comp (mapRingHom (Int.castRingHom k)) := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp [evalAtLambdaInt]
    · simp [evalAtLambdaInt, lambdaModC]
  exact RingHom.congr_fun h P

theorem main (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (data : LambdaModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
            + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (k : Type*) [Field k] [CharP k q] :
    let G : Polynomial k := (R.eval (Polynomial.X ^ q)).map (Int.castRingHom k)
    let F : Polynomial k := Polynomial.X ^ (q ^ 2) - Polynomial.X
    let H : Polynomial k := ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)).comp (16 * Polynomial.X)
    (Polynomial.derivative G * F - G * Polynomial.derivative F) * H ^ 2 =
      (Polynomial.X ^ (q - 1) * H ^ 2 - (Polynomial.X * (1 - 16 * Polynomial.X)) ^ (q - 1)) * F ^ 2 := by
  intro G F H
  have hp : q.Prime := Fact.out
  have h8 := deuringPolynomial_sq_mul_thetaL_lambda_pow q hq k
  set ι := Int.castRingHom k with hι
  set J : LaurentSeries k := lambdaModC k with hJ
  set θ := thetaL k with hθ
  have hinj : Function.Injective (aeval J : Polynomial k →ₐ[k] LaurentSeries k) := aeval_lambdaModC_injective
  obtain ⟨S, hS, -⟩ := existsUnique_qExpand_sub_pow_eq_natCast_mul q lambdaInt
  have hA : aeval J G = - laurentMap ι S * aeval J F := by
    have h := laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow q data R hR S hS k
    rw [laurentMap_evalAtLambdaInt] at h
    rw [h]
    simp [F, hJ, hι]
  have hB : θ (laurentMap ι S) = θ J ^ q - J ^ (q - 1) * θ J :=
    thetaL_laurentMap_lambdaDworkQuotient q S hS k
  have hC : θ J ^ (q - 1) * aeval J H ^ 2 = (J * (1 - 16 * J)) ^ (q - 1) := by
    have h16 : aeval J (16 * Polynomial.X : Polynomial k) = 16 * J := by
      rw [map_mul, aeval_X, map_ofNat]
    have hH : aeval J H = aeval (16 * J) ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)) := by
      rw [show H = ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)).comp (16 * Polynomial.X) from rfl,
        Polynomial.aeval_comp, h16]
    rw [hH, mul_comm]
    exact h8
  have hF' : derivative F = -1 := by
    simp only [F, derivative_sub, derivative_X_pow, derivative_X, Nat.cast_pow]
    rw [CharP.cast_eq_zero k q] ; simp
  have hθJ : θ J ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x : LaurentSeries k => x.coeff 1) h0
    simp only [hθ, thetaL_eq_thetaR, coeff_thetaR, HahnSeries.coeff_zero, hJ, coeff_lambdaModC_one,
      Int.cast_one, mul_one] at h1
    exact one_ne_zero h1
  have hq1 : q = (q - 1) + 1 := (Nat.succ_pred_eq_of_pos hp.pos).symm
  have hstar : aeval J (derivative G) * aeval J F + aeval J G =
      (J ^ (q - 1) - θ J ^ (q - 1)) * aeval J F ^ 2 := by
    have h1 := congrArg θ hA
    rw [hθ, thetaL_aeval, neg_mul, map_neg, thetaL_eq_thetaR (laurentMap ι S * aeval J F), thetaR_mul,
      ← thetaL_eq_thetaR, ← thetaL_eq_thetaR, thetaL_aeval, hF', ← hθ, hB] at h1
    simp only [map_neg, map_one] at h1
    have h2 : θ J * (aeval J (derivative G) * aeval J F + aeval J G
        - (J ^ (q - 1) - θ J ^ (q - 1)) * aeval J F ^ 2) = 0 := by
      have e : θ J ^ q = θ J ^ (q - 1) * θ J := by
        conv_lhs => rw [hq1]
        rw [pow_succ]
      rw [e] at h1
      linear_combination (aeval J F) * h1 + (θ J) * hA
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hθJ
    · exact sub_eq_zero.mp h
  apply hinj
  simp only [map_mul, map_sub, map_pow, hF', map_neg, map_one, aeval_X, map_ofNat]
  rw [← hC]
  linear_combination (aeval J H ^ 2) * hstar

end ModularCurve.L9

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (data : LambdaModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (k : Type*) [Field k] [CharP k q] :
    let G : Polynomial k := (R.eval (Polynomial.X ^ q)).map (Int.castRingHom k)
    let F : Polynomial k := Polynomial.X ^ (q ^ 2) - Polynomial.X
    let H : Polynomial k := ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)).comp (16 * Polynomial.X)
    (Polynomial.derivative G * F - G * Polynomial.derivative F) * H ^ 2 =
      (Polynomial.X ^ (q - 1) * H ^ 2 - (Polynomial.X * (1 - 16 * Polynomial.X)) ^ (q - 1)) * F ^ 2 :=
  ModularCurve.L9.main q hq data R hR k

end S_ModularCurve_lambdaKroneckerRemainder_frobeniusGraph_ode
end P2MW
export P2MW.S_ModularCurve_lambdaKroneckerRemainder_frobeniusGraph_ode (solution)
