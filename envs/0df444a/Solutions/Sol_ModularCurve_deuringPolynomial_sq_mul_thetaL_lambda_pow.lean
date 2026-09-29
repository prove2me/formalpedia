-- Prove2me | solution 1 for ModularCurve.deuringPolynomial_sq_mul_thetaL_lambda_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/fc897eaf-9254-505e-a934-9a387e9c249e

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_delta_pow_mul_deuringPolynomial_lambda_pow_twelve
import Theorems.Thm_ModularCurve_thetaL_lambdaModC_pow_six
import Theorems.Thm_Polynomial_eval_zero_deuringPolynomial_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_deuringPolynomial_sq_mul_thetaL_lambda_pow
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false

p2m_open "HahnSeries Polynomial ModularCurve P2MW.S_ModularCurve_deuringPolynomial_sq_mul_thetaL_lambda_pow.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd etaProd constantCoeff_etaProd dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv ofPowerSeries_coeff_of_neg lambdaInt lambdaModC laurentMap laurentMap_coeff laurentMap_single laurentMap_ofPowerSeries laurentMap_qExpand laurentMap_injective thetaL thetaL_apply delta_pow_mul_deuringPolynomial_lambda_pow_twelve thetaL_lambdaModC_pow_six"
namespace L8
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

end LambdaNorm

section Norm

variable {k : Type*} [Field k]

def Norm (A : LaurentSeries k) (a : ℤ) : Prop := A ≠ 0 ∧ A.order = a ∧ A.leadingCoeff = 1

theorem Norm.of_coeff {A : LaurentSeries k} {a : ℤ} (h1 : A.coeff a = 1) (h2 : ∀ n < a, A.coeff n = 0) : Norm A a := by
  have h1' : A.coeff a ≠ 0 := by rw [h1]; exact one_ne_zero
  exact ⟨HahnSeries.ne_zero_of_coeff_ne_zero h1', order_eq_of_coeff h1' h2, by rw [leadingCoeff_eq_of_coeff h1' h2, h1]⟩

theorem Norm.mul {A B : LaurentSeries k} {a b : ℤ} (hA : Norm A a) (hB : Norm B b) : Norm (A * B) (a + b) :=
  ⟨mul_ne_zero hA.1 hB.1, by rw [order_mul' hA.1 hB.1, hA.2.1, hB.2.1],
    by rw [leadingCoeff_mul' hA.1 hB.1, hA.2.2, hB.2.2, mul_one]⟩

theorem Norm.pow {A : LaurentSeries k} {a : ℤ} (hA : Norm A a) (n : ℕ) : Norm (A ^ n) (n * a) :=
  ⟨pow_ne_zero n hA.1, by rw [order_pow' hA.1, hA.2.1, nsmul_eq_mul], by rw [leadingCoeff_pow' hA.1, hA.2.2, one_pow]⟩

theorem Norm.coeff_self {A : LaurentSeries k} {a : ℤ} (hA : Norm A a) : A.coeff a = 1 := by
  rw [← hA.2.1, ← HahnSeries.leadingCoeff_eq]; exact hA.2.2

theorem Norm.coeff_lt {A : LaurentSeries k} {a : ℤ} (hA : Norm A a) {n : ℤ} (hn : n < a) : A.coeff n = 0 :=
  HahnSeries.coeff_eq_zero_of_lt_order (by rw [hA.2.1]; exact hn)

theorem eq_of_pow_six_eq {X Y : LaurentSeries k} {a : ℤ} (hX : Norm X a) (hY : Norm Y a) (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h : X ^ 6 = Y ^ 6) : X = Y := by
  have hfac : (X - Y) * ((X + Y) * ((X ^ 2 + X * Y + Y ^ 2) * (X ^ 2 - X * Y + Y ^ 2))) = X ^ 6 - Y ^ 6 := by ring
  rw [h, sub_self] at hfac
  have hXY : Norm (X * Y) (a + a) := hX.mul hY
  have hX2 : Norm (X ^ 2) (a + a) := by have := hX.pow 2; rwa [show (2 : ℕ) * a = a + a by ring] at this
  have hY2 : Norm (Y ^ 2) (a + a) := by have := hY.pow 2; rwa [show (2 : ℕ) * a = a + a by ring] at this
  have hne1 : X + Y ≠ 0 := by
    apply HahnSeries.ne_zero_of_coeff_ne_zero (g := a)
    rw [HahnSeries.coeff_add, hX.coeff_self, hY.coeff_self]; norm_num; exact h2
  have hne2 : X ^ 2 + X * Y + Y ^ 2 ≠ 0 := by
    apply HahnSeries.ne_zero_of_coeff_ne_zero (g := a + a)
    rw [HahnSeries.coeff_add, HahnSeries.coeff_add, hX2.coeff_self, hXY.coeff_self, hY2.coeff_self]; norm_num; exact h3
  have hne3 : X ^ 2 - X * Y + Y ^ 2 ≠ 0 := by
    apply HahnSeries.ne_zero_of_coeff_ne_zero (g := a + a)
    rw [HahnSeries.coeff_add, HahnSeries.coeff_sub, hX2.coeff_self, hXY.coeff_self, hY2.coeff_self]; norm_num
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 (mul_ne_zero hne1 (mul_ne_zero hne2 hne3))

end Norm

section Concrete

variable {k : Type*} [Field k]

theorem norm_lambdaModC : Norm (lambdaModC k) 1 := Norm.of_coeff coeff_lambdaModC_one fun n hn => coeff_lambdaModC_of_lt hn

theorem norm_one_sub : Norm (1 - 16 * lambdaModC k) 0 := by
  refine Norm.of_coeff ?_ (fun n hn => ?_)
  · rw [HahnSeries.coeff_sub, HahnSeries.coeff_one, if_pos rfl, show (16 : LaurentSeries k) = ((16 : ℕ) : LaurentSeries k) by norm_num,
      ← map_natCast (HahnSeries.C (Γ := ℤ) (R := k)) 16, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      coeff_lambdaModC_of_lt (by norm_num), smul_zero, sub_zero]
  · rw [HahnSeries.coeff_sub, HahnSeries.coeff_one, if_neg hn.ne, show (16 : LaurentSeries k) = ((16 : ℕ) : LaurentSeries k) by norm_num,
      ← map_natCast (HahnSeries.C (Γ := ℤ) (R := k)) 16, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      coeff_lambdaModC_of_lt (by omega), smul_zero, sub_zero]

theorem norm_thetaL : Norm (thetaL k (lambdaModC k)) 1 := by
  have hc : ∀ n : ℤ, (thetaL k (lambdaModC k)).coeff n = (n : k) * (lambdaModC k).coeff n := fun n => by
    rw [thetaL_apply, coeff_single_one_mul_derivative]
  refine Norm.of_coeff ?_ (fun n hn => ?_)
  · rw [hc, coeff_lambdaModC_one, Int.cast_one, one_mul]
  · rw [hc, coeff_lambdaModC_of_lt hn, mul_zero]

theorem coeff_mul_eq_zero_of_lt' {A B : LaurentSeries k} {a b : ℤ} (ha : ∀ n < a, A.coeff n = 0)
    (hb : ∀ n < b, B.coeff n = 0) {n : ℤ} (hn : n < a + b) : (A * B).coeff n = 0 := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨h1, h2, h3⟩ := hij
  exfalso
  by_cases hi : ij.1 < a
  · exact (HahnSeries.mem_support _ _).mp h1 (ha _ hi)
  · exact (HahnSeries.mem_support _ _).mp h2 (hb _ (by omega))

theorem coeff_pow_eq_zero_of_lt {A : LaurentSeries k} (ha : ∀ n < 1, A.coeff n = 0) (i : ℕ) {n : ℤ} (hn : n < i) :
    (A ^ i).coeff n = 0 := by
  induction i generalizing n with
  | zero => rw [pow_zero, HahnSeries.coeff_one, if_neg (by omega)]
  | succ i ih =>
    rw [pow_succ]
    exact coeff_mul_eq_zero_of_lt' (a := i) (b := 1) (fun m hm => ih hm) ha (by push_cast at hn; omega)

theorem norm_aeval_deuring (q : ℕ) :
    Norm (Polynomial.aeval (16 * lambdaModC k) ((Polynomial.deuringPolynomial q).map (Int.castRingHom k))) 0 := by
  set P := (Polynomial.deuringPolynomial q).map (Int.castRingHom k) with hP
  set M : LaurentSeries k := 16 * lambdaModC k with hM
  have hMlt : ∀ n < 1, M.coeff n = 0 := fun n hn => by
    rw [hM, show (16 : LaurentSeries k) = ((16 : ℕ) : LaurentSeries k) by norm_num,
      ← map_natCast (HahnSeries.C (Γ := ℤ) (R := k)) 16, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      coeff_lambdaModC_of_lt hn, smul_zero]
  have hsum : ∀ n : ℤ, (Polynomial.aeval M P).coeff n
      = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (M ^ i).coeff n := by
    intro n
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, LaurentSeries.algebraMap_apply, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  refine Norm.of_coeff ?_ (fun n hn => ?_)
  · rw [hsum, Finset.sum_eq_single 0]
    · rw [pow_zero, HahnSeries.coeff_one, if_pos rfl, mul_one, Polynomial.coeff_zero_eq_eval_zero, hP,
        Polynomial.eval_zero_deuringPolynomial_map]
    · intro i _ hi0
      rw [coeff_pow_eq_zero_of_lt hMlt i (by have := Nat.pos_of_ne_zero hi0; exact_mod_cast this), mul_zero]
    · intro h; exfalso; exact h (Finset.mem_range.mpr (Nat.succ_pos _))
  · rw [hsum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [coeff_pow_eq_zero_of_lt hMlt i (by have := Int.natCast_nonneg i; omega), mul_zero]

theorem norm_delta_two :
    Norm (ModularCurve.qExpand k 2 (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit)))) 2 := by
  set D := HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit)) with hD
  have hnat : ∀ n : ℕ, D.coeff (n : ℤ) = PowerSeries.coeff n (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit)) :=
    fun n => HahnSeries.ofPowerSeries_apply_coeff _ n
  have h1 : D.coeff 1 = 1 := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, hnat, PowerSeries.coeff_map, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_dedekindEtaUnit, map_one]
  have h2 : ∀ n < (1 : ℤ), D.coeff n = 0 := by
    intro n hn
    rcases lt_or_eq_of_le (show n ≤ 0 by omega) with hneg | rfl
    · exact ofPowerSeries_coeff_of_neg _ hneg
    · rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, hnat, PowerSeries.coeff_map, PowerSeries.coeff_zero_X_mul, map_zero]
  refine Norm.of_coeff ?_ (fun n hn => ?_)
  · have h := qExpand_coeff_mul (R := k) 2 D 1
    rw [mul_one, Nat.cast_ofNat] at h
    rw [h, h1]
  · by_cases hd : (2 : ℤ) ∣ n
    · obtain ⟨c, rfl⟩ := hd
      have h := qExpand_coeff_mul (R := k) 2 D c
      rw [Nat.cast_ofNat] at h
      rw [h]; exact h2 c (by omega)
    · exact qExpand_coeff_of_not_dvd 2 D (by exact_mod_cast hd)

end Concrete

theorem theta_pow_six (k : Type*) [Field k] :
    thetaL k (lambdaModC k) ^ 6 = lambdaModC k ^ 4 * (1 - 16 * lambdaModC k) ^ 4 *
      ModularCurve.qExpand k 2 (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit))) := by
  have hZ : thetaR lambdaInt ^ 6 = lambdaInt ^ 4 * (1 - 16 * lambdaInt) ^ 4 *
      ModularCurve.qExpand ℤ 2 (HahnSeries.single (1 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit) := by
    apply laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
    rw [map_pow, laurentMap_thetaR, map_mul, map_mul, map_pow, map_pow, map_sub, map_one, map_mul, map_ofNat,
      laurentMap_qExpand, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]
    exact thetaL_lambdaModC_pow_six
  have h := congrArg (laurentMap (Int.castRingHom k)) hZ
  rw [map_pow, laurentMap_thetaR, map_mul, map_mul, map_pow, map_pow, map_sub, map_one, map_mul, map_ofNat,
    laurentMap_qExpand, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one] at h
  rw [lambdaModC] at *
  rw [h]
  congr 2
  rw [map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X]

theorem main (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q] :
    (Polynomial.aeval (16 * lambdaModC k) ((Polynomial.deuringPolynomial q).map (Int.castRingHom k))) ^ 2 * thetaL k (lambdaModC k) ^ (q - 1)
      = (lambdaModC k * (1 - 16 * lambdaModC k)) ^ (q - 1) := by
  have hp : q.Prime := Fact.out
  have hcast : ∀ a : ℕ, 0 < a → a < q → (a : k) ≠ 0 := fun a ha haq h =>
    absurd (Nat.le_of_dvd ha ((CharP.cast_eq_zero_iff k q a).mp h)) (not_le.mpr haq)
  have h2 : (2 : k) ≠ 0 := by exact_mod_cast hcast 2 (by norm_num) (by omega)
  have h3 : (3 : k) ≠ 0 := by exact_mod_cast hcast 3 (by norm_num) (by omega)
  set H := Polynomial.aeval (16 * lambdaModC k) ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)) with hH
  set T := thetaL k (lambdaModC k) with hT
  set μ := lambdaModC k with hμ
  set D := ModularCurve.qExpand k 2 (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit))) with hD
  have hF : D ^ (q - 1) * H ^ 12 = (μ * (1 - 16 * μ)) ^ (2 * (q - 1)) := delta_pow_mul_deuringPolynomial_lambda_pow_twelve q hq k
  have hJ : T ^ 6 = μ ^ 4 * (1 - 16 * μ) ^ 4 * D := theta_pow_six k

  have hX : Norm (H ^ 2 * T ^ (q - 1)) ((q - 1 : ℕ) : ℤ) := by
    have h := ((norm_aeval_deuring (k := k) q).pow 2).mul (norm_thetaL.pow (q - 1))
    simpa using h
  have hY : Norm ((μ * (1 - 16 * μ)) ^ (q - 1)) ((q - 1 : ℕ) : ℤ) := by
    have h := ((norm_lambdaModC (k := k)).mul norm_one_sub).pow (q - 1)
    simpa using h
  apply eq_of_pow_six_eq hX hY h2 h3
  set ν : LaurentSeries k := 1 - 16 * μ with hν
  calc (H ^ 2 * T ^ (q - 1)) ^ 6 = H ^ 12 * (T ^ 6) ^ (q - 1) := by ring
    _ = H ^ 12 * (μ ^ 4 * ν ^ 4 * D) ^ (q - 1) := by rw [hJ]
    _ = (D ^ (q - 1) * H ^ 12) * (μ * ν) ^ (4 * (q - 1)) := by ring
    _ = (μ * ν) ^ (2 * (q - 1)) * (μ * ν) ^ (4 * (q - 1)) := by rw [hF]
    _ = ((μ * ν) ^ (q - 1)) ^ 6 := by ring

end ModularCurve.L8

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q] :
    (Polynomial.aeval (16 * lambdaModC k) ((Polynomial.deuringPolynomial q).map (Int.castRingHom k))) ^ 2 * thetaL k (lambdaModC k) ^ (q - 1)
      = (lambdaModC k * (1 - 16 * lambdaModC k)) ^ (q - 1) :=
  ModularCurve.L8.main q hq k

end S_ModularCurve_deuringPolynomial_sq_mul_thetaL_lambda_pow
end P2MW
export P2MW.S_ModularCurve_deuringPolynomial_sq_mul_thetaL_lambda_pow (solution)
