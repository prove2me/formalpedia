-- Prove2me | solution 1 for ModularCurve.thetaL_jqModC_pow_mul_prod_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b63bbae1-4b92-5eb4-a01a-d79c568e9cb4

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_delta_pow_mul_prod_jqModC_sub_pow_eq_one
import Theorems.Thm_ModularCurve_thetaL_jq_pow_six
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "HahnSeries Polynomial ModularCurve P2MW.S_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd dedekindEtaUnit constantCoeff_dedekindEtaUnit ofPowerSeries_coeff_of_neg thetaL thetaL_apply ssJSet laurentMap laurentMap_coeff laurentMap_single laurentMap_ofPowerSeries laurentMap_injective jqInt laurentMap_jqInt coeff_jqInt_neg_one coeff_jqInt_of_lt jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne delta_pow_mul_prod_jqModC_sub_pow_eq_one thetaL_jq_pow_six"
namespace K2cor
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

theorem laurentMap_jqInt_eq_jqModC (k : Type*) [CommRing k] :
    laurentMap (Int.castRingHom k) jqInt = jqModC k := by
  rw [jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]
  rfl

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

section Concrete

variable (k : Type*) [Field k]

theorem coeff_jqModC_neg_one : (jqModC k).coeff (-1) = 1 := by
  rw [← laurentMap_jqInt_eq_jqModC, laurentMap_coeff, coeff_jqInt_neg_one, map_one]

theorem coeff_jqModC_of_lt {n : ℤ} (hn : n < -1) : (jqModC k).coeff n = 0 := by
  rw [← laurentMap_jqInt_eq_jqModC, laurentMap_coeff, coeff_jqInt_of_lt hn, map_zero]

theorem jqModC_ne_zero : jqModC k ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero (by rw [coeff_jqModC_neg_one]; exact one_ne_zero)

theorem order_jqModC : (jqModC k).order = -1 :=
  order_eq_of_coeff (by rw [coeff_jqModC_neg_one]; exact one_ne_zero) fun n hn => coeff_jqModC_of_lt k hn

theorem leadingCoeff_jqModC : (jqModC k).leadingCoeff = 1 := by
  rw [leadingCoeff_eq_of_coeff (by rw [coeff_jqModC_neg_one]; exact one_ne_zero)
    fun n hn => coeff_jqModC_of_lt k hn, coeff_jqModC_neg_one]

variable {k}

theorem coeff_C_of_ne (a : k) {n : ℤ} (hn : n ≠ 0) : (HahnSeries.C a : LaurentSeries k).coeff n = 0 := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn]

theorem sub_C_facts (a : k) :
    (jqModC k - HahnSeries.C a) ≠ 0 ∧ (jqModC k - HahnSeries.C a).order = -1 ∧
      (jqModC k - HahnSeries.C a).leadingCoeff = 1 := by
  have h1 : (jqModC k - HahnSeries.C a).coeff (-1) = 1 := by
    rw [HahnSeries.coeff_sub, coeff_jqModC_neg_one, coeff_C_of_ne a (by norm_num), sub_zero]
  have h2 : ∀ n < (-1 : ℤ), (jqModC k - HahnSeries.C a).coeff n = 0 := fun n hn => by
    rw [HahnSeries.coeff_sub, coeff_jqModC_of_lt k hn, coeff_C_of_ne a (by omega), sub_zero]
  have h1' : (jqModC k - HahnSeries.C a).coeff (-1) ≠ 0 := by rw [h1]; exact one_ne_zero
  exact ⟨HahnSeries.ne_zero_of_coeff_ne_zero h1', order_eq_of_coeff h1' h2,
    by rw [leadingCoeff_eq_of_coeff h1' h2, h1]⟩

theorem theta_facts :
    thetaL k (jqModC k) ≠ 0 ∧ (thetaL k (jqModC k)).order = -1 ∧
      (thetaL k (jqModC k)).leadingCoeff = -1 := by
  have hc : ∀ n : ℤ, (thetaL k (jqModC k)).coeff n = (n : k) * (jqModC k).coeff n := fun n => by
    rw [thetaL_apply, coeff_single_one_mul_derivative]
  have h1 : (thetaL k (jqModC k)).coeff (-1) = -1 := by
    rw [hc, coeff_jqModC_neg_one, mul_one, Int.cast_neg, Int.cast_one]
  have h2 : ∀ n < (-1 : ℤ), (thetaL k (jqModC k)).coeff n = 0 := fun n hn => by
    rw [hc, coeff_jqModC_of_lt k hn, mul_zero]
  have h1' : (thetaL k (jqModC k)).coeff (-1) ≠ 0 := by rw [h1]; exact neg_ne_zero.mpr one_ne_zero
  exact ⟨HahnSeries.ne_zero_of_coeff_ne_zero h1', order_eq_of_coeff h1' h2,
    by rw [leadingCoeff_eq_of_coeff h1' h2, h1]⟩

theorem delta_eq (R : Type*) [CommRing R] :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.map (Int.castRingHom R) (PowerSeries.X * dedekindEtaUnit)) =
      HahnSeries.single (1 : ℤ) (1 : R) *
        HahnSeries.ofPowerSeries ℤ R (PowerSeries.map (Int.castRingHom R) dedekindEtaUnit) := by
  rw [map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X]

theorem delta_facts :
    HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit)) ≠ 0 ∧
    (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit))).order = 1 ∧
    (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit))).leadingCoeff = 1 := by
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
  have h1' : D.coeff 1 ≠ 0 := by rw [h1]; exact one_ne_zero
  exact ⟨HahnSeries.ne_zero_of_coeff_ne_zero h1', order_eq_of_coeff h1' h2,
    by rw [leadingCoeff_eq_of_coeff h1' h2, h1]⟩

end Concrete

theorem theta_pow_six (k : Type*) [Field k] :
    thetaL k (jqModC k) ^ 6 = jqModC k ^ 4 * (jqModC k - 1728) ^ 3 *
      HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit)) := by

  have hZ : thetaR jqInt ^ 6 = jqInt ^ 4 * (jqInt - 1728) ^ 3 *
      (HahnSeries.single (1 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit) := by
    apply laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
    rw [map_pow, laurentMap_thetaR, map_mul, map_mul, map_mul, map_pow, map_pow, map_sub,
      laurentMap_single, laurentMap_ofPowerSeries, laurentMap_jqInt, map_ofNat, map_one]
    exact thetaL_jq_pow_six
  have h := congrArg (laurentMap (Int.castRingHom k)) hZ
  rw [map_pow, laurentMap_thetaR, map_mul, map_mul, map_mul, map_pow, map_pow, map_sub,
    laurentMap_single, laurentMap_ofPowerSeries, laurentMap_jqInt_eq_jqModC, map_ofNat, map_one,
    ← delta_eq] at h
  exact h

theorem cast_1728_ne_zero (q : ℕ) (hp : q.Prime) (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q] :
    (1728 : k) ≠ 0 := by
  intro h
  have h' : ((1728 : ℕ) : k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff k q] at h'
  have : q ∣ 2 ^ 6 * 3 ^ 3 := by norm_num at h' ⊢; exact h'
  rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hp h2); omega
  · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hp h3); omega

theorem main (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = q - 1) (he₄ : e₄ ≤ 2) (he₆ : e₆ ≤ 1)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    thetaL k (jqModC k) ^ (q - 1) *
        (∏ a ∈ S₀ \ {0, 1728}, (jqModC k - HahnSeries.C a)) ^ 2 =
      jqModC k ^ (8 * m + 2 * e₄ + 4 * e₆) * (jqModC k - 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) := by
  have hp : q.Prime := Fact.out
  have h1728 : (1728 : k) ≠ 0 := cast_1728_ne_zero q hp hq k
  set J := jqModC k with hJ
  set T := thetaL k (jqModC k) with hT
  set D := HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit)) with hD
  set s := ∏ a ∈ S₀ \ {0, 1728}, (J - HahnSeries.C a) with hs
  set n₁ : ℕ := (S₀ \ {0, 1728}).card with hn₁
  set ε₀ : ℕ := if (0 : k) ∈ S₀ then 1 else 0 with hε₀
  set ε₁ : ℕ := if (1728 : k) ∈ S₀ then 1 else 0 with hε₁
  have hε₀1 : ε₀ ≤ 1 := by rw [hε₀]; split_ifs <;> omega
  have hε₁1 : ε₁ ≤ 1 := by rw [hε₁]; split_ifs <;> omega
  obtain ⟨hJ0, hJord, hJlc⟩ : J ≠ 0 ∧ J.order = -1 ∧ J.leadingCoeff = 1 :=
    ⟨jqModC_ne_zero k, order_jqModC k, leadingCoeff_jqModC k⟩
  obtain ⟨hT0, hTord, hTlc⟩ : T ≠ 0 ∧ T.order = -1 ∧ T.leadingCoeff = -1 := theta_facts
  obtain ⟨hD0, hDord, hDlc⟩ : D ≠ 0 ∧ D.order = 1 ∧ D.leadingCoeff = 1 := delta_facts
  have hJa : ∀ a : k, (J - HahnSeries.C a) ≠ 0 ∧ (J - HahnSeries.C a).order = -1 ∧
      (J - HahnSeries.C a).leadingCoeff = 1 := fun a => sub_C_facts a
  obtain ⟨hJ17280, hJ1728ord, hJ1728lc⟩ : (J - 1728) ≠ 0 ∧ (J - 1728).order = -1 ∧
      (J - 1728).leadingCoeff = 1 := by
    have h := hJa 1728; rwa [map_ofNat] at h
  have hs0 : s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => (hJa a).1
  have hsord : s.order = -(n₁ : ℤ) := by
    rw [hs, order_prod' _ _ fun a _ => (hJa a).1]
    rw [Finset.sum_congr rfl fun a _ => (hJa a).2.1, Finset.sum_const, smul_neg, nsmul_eq_mul, mul_one]
  have hslc : s.leadingCoeff = 1 := by
    rw [hs, leadingCoeff_prod' _ _ fun a _ => (hJa a).1]
    exact Finset.prod_eq_one fun a _ => (hJa a).2.2

  have hc1 : T ^ 6 = J ^ 4 * (J - 1728) ^ 3 * D := theta_pow_six k

  have hFACE := delta_pow_mul_prod_jqModC_sub_pow_eq_one q hq k S₀ hS₀
  have hsplit : ∀ (g : k → LaurentSeries k),
      ∏ a ∈ S₀, g a = (∏ a ∈ S₀ \ {0, 1728}, g a) *
        ((if (0 : k) ∈ S₀ then g 0 else 1) * (if (1728 : k) ∈ S₀ then g 1728 else 1)) := by
    intro g
    have h1 : ∏ a ∈ S₀, g a = (∏ a ∈ S₀ \ {0, 1728}, g a) * ∏ a ∈ S₀ ∩ {0, 1728}, g a := by
      rw [← Finset.prod_sdiff (Finset.inter_subset_left (s₁ := S₀) (s₂ := {0, 1728})),
        Finset.sdiff_inter_self_left]
    have h2 : ∏ a ∈ S₀ ∩ {0, 1728}, g a = ∏ a ∈ ({0, 1728} : Finset k), (if a ∈ S₀ then g a else 1) := by
      rw [Finset.prod_ite_mem, Finset.inter_comm]
    rw [h1, h2, Finset.prod_pair h1728.symm]
  have hP : ∏ a ∈ S₀, (J - HahnSeries.C a) ^ (12 / jWidth a) =
      s ^ 12 * (J ^ (4 * ε₀) * (J - 1728) ^ (6 * ε₁)) := by
    rw [hsplit]
    congr 1
    · rw [hs, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun a ha => ?_
      rw [Finset.mem_sdiff] at ha
      have ha' : a ≠ 0 ∧ a ≠ 1728 := by simpa using ha.2
      rw [jWidth_of_ne ha'.1 ha'.2]
    · congr 1
      · rw [hε₀, map_zero, sub_zero, jWidth_of_eq_zero rfl]
        split_ifs <;> norm_num
      · rw [hε₁, map_ofNat, jWidth_of_eq_1728 rfl h1728]
        split_ifs <;> norm_num
  rw [hP] at hFACE
  change D ^ (q - 1) * (s ^ 12 * (J ^ (4 * ε₀) * (J - 1728) ^ (6 * ε₁))) = 1 at hFACE

  have hord := congrArg HahnSeries.order hFACE
  rw [HahnSeries.order_one, order_mul' (pow_ne_zero _ hD0) (mul_ne_zero (pow_ne_zero _ hs0)
      (mul_ne_zero (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ17280))),
    order_mul' (pow_ne_zero _ hs0) (mul_ne_zero (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ17280)),
    order_mul' (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ17280),
    order_pow' hD0, order_pow' hs0, order_pow' hJ0, order_pow' hJ17280,
    hDord, hsord, hJord, hJ1728ord] at hord
  simp only [smul_eq_mul, mul_one, mul_neg, nsmul_eq_mul] at hord
  have hq1 : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  have hkey : ε₀ = e₄ ∧ ε₁ = e₆ ∧ n₁ = m := by omega
  obtain ⟨hε₀e, hε₁e, hn₁m⟩ := hkey
  rw [hε₀e, hε₁e] at hFACE

  set X := T ^ (q - 1) * s ^ 2 with hX
  set Y := J ^ (8 * m + 2 * e₄ + 4 * e₆) * (J - 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) with hY
  set W := J ^ (4 * e₄) * (J - 1728) ^ (6 * e₆) with hW
  have hW0 : W ≠ 0 := mul_ne_zero (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ17280)
  have h4 : 4 * (q - 1) = 6 * (8 * m + 2 * e₄ + 4 * e₆) + 4 * e₄ := by omega
  have h3 : 3 * (q - 1) = 6 * (6 * m + 2 * e₄ + 2 * e₆) + 6 * e₆ := by omega
  have hX6 : X ^ 6 * W = J ^ (4 * (q - 1)) * (J - 1728) ^ (3 * (q - 1)) := by
    have e1 : X ^ 6 = (T ^ 6) ^ (q - 1) * s ^ 12 := by
      rw [hX, mul_pow, ← pow_mul, ← pow_mul, mul_comm (q - 1) 6, pow_mul]
    rw [e1, hc1, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    have e2 : J ^ (4 * (q - 1)) * (J - 1728) ^ (3 * (q - 1)) * D ^ (q - 1) * s ^ 12 * W
        = J ^ (4 * (q - 1)) * (J - 1728) ^ (3 * (q - 1)) * (D ^ (q - 1) * (s ^ 12 * W)) := by ring
    rw [e2, hFACE, mul_one]
  have hY6 : Y ^ 6 * W = J ^ (4 * (q - 1)) * (J - 1728) ^ (3 * (q - 1)) := by
    rw [hY, hW, h4, h3]; ring
  have h66 : X ^ 6 = Y ^ 6 := mul_right_cancel₀ hW0 (hX6.trans hY6.symm)

  have hY0 : Y ≠ 0 := mul_ne_zero (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ17280)
  have hX0 : X ≠ 0 := mul_ne_zero (pow_ne_zero _ hT0) (pow_ne_zero _ hs0)
  set u := X * Y⁻¹ with hu
  have hu6 : u ^ 6 = 1 := by
    rw [hu, mul_pow, h66, ← mul_pow, mul_inv_cancel₀ hY0, one_pow]
  have hint : IsIntegral k u := by
    refine ⟨Polynomial.X ^ 6 - 1, Polynomial.monic_X_pow_sub_C 1 (by norm_num), ?_⟩
    simp [hu6]
  have hdeg : (minpoly k u).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ : u ∈ (algebraMap k (LaurentSeries k)).range := minpoly.mem_range_of_degree_eq_one k u hdeg
  rw [LaurentSeries.algebraMap_apply] at hc
  have hXcY : X = HahnSeries.C c * Y := by
    rw [hc, hu, mul_assoc, inv_mul_cancel₀ hY0, mul_one]

  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [HahnSeries.C_zero, zero_mul] at hXcY
    exact hX0 hXcY
  have heven : Even (q - 1) := hp.even_sub_one (by omega)
  have hXlc : X.leadingCoeff = 1 := by
    rw [hX, leadingCoeff_mul' (pow_ne_zero _ hT0) (pow_ne_zero _ hs0), leadingCoeff_pow' hT0,
      leadingCoeff_pow' hs0, hTlc, hslc, heven.neg_one_pow, one_pow, one_mul]
  have hYlc : Y.leadingCoeff = 1 := by
    rw [hY, leadingCoeff_mul' (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ17280), leadingCoeff_pow' hJ0,
      leadingCoeff_pow' hJ17280, hJlc, hJ1728lc, one_pow, one_pow, one_mul]
  have hClc : (HahnSeries.C c : LaurentSeries k).leadingCoeff = c := by
    rw [HahnSeries.C_apply, HahnSeries.leadingCoeff_of_single]
  have hC0 : (HahnSeries.C c : LaurentSeries k) ≠ 0 := by
    intro h; exact hc0 (HahnSeries.C_injective (h.trans HahnSeries.C_zero.symm))
  have hcmp := congrArg HahnSeries.leadingCoeff hXcY
  rw [hXlc, leadingCoeff_mul' hC0 hY0, hClc, hYlc, mul_one] at hcmp
  rw [hXcY, ← hcmp, HahnSeries.C_one, one_mul]

end ModularCurve.K2cor

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = q - 1) (he₄ : e₄ ≤ 2) (he₆ : e₆ ≤ 1)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    thetaL k (jqModC k) ^ (q - 1) *
        (∏ a ∈ S₀ \ {0, 1728}, (jqModC k - HahnSeries.C a)) ^ 2 =
      jqModC k ^ (8 * m + 2 * e₄ + 4 * e₆) * (jqModC k - 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) :=
  ModularCurve.K2cor.main q hq m e₄ e₆ hm he₄ he₆ k S₀ hS₀

end S_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq
end P2MW
export P2MW.S_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq (solution)
