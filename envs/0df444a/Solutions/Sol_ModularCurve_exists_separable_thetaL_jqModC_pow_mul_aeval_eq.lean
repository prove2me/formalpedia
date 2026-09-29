-- Prove2me | solution 1 for ModularCurve.exists_separable_thetaL_jqModC_pow_mul_aeval_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/80931a47-916d-51a2-a8c8-0931c3fdcb75

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_self
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_of_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_separable_thetaL_jqModC_pow_mul_aeval_eq
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

namespace AKATZSSH

open ModularCurve Polynomial

section Tools

variable {K : Type*} [Field K]

theorem thetaL_coeff (f : LaurentSeries K) (n : ℤ) :
    (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply, ModularCurve.theta_coeff, zsmul_eq_mul]

theorem coeff_ofNat_1728 (n : ℤ) (hn : n ≠ 0) : (1728 : LaurentSeries K).coeff n = 0 := by
  rw [show (1728 : LaurentSeries K) = algebraMap K (LaurentSeries K) 1728 from
      (map_ofNat (algebraMap K (LaurentSeries K)) 1728).symm,
    algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne hn]

theorem order_eq_of_coeff {f : LaurentSeries K} {n : ℤ} (h0 : f.coeff n ≠ 0)
    (h : ∀ k < n, f.coeff k = 0) : f.order = n := by
  have hf : f ≠ 0 := fun hf => h0 (by rw [hf, HahnSeries.coeff_zero])
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h0) ?_
  by_contra hlt
  push Not at hlt
  exact (mt HahnSeries.coeff_order_eq_zero.mp hf) (h _ hlt)

theorem leadingCoeff_eq_coeff {f : LaurentSeries K} {n : ℤ} (h0 : f.coeff n ≠ 0)
    (h : ∀ k < n, f.coeff k = 0) : f.leadingCoeff = f.coeff n := by
  rw [HahnSeries.leadingCoeff_eq, order_eq_of_coeff h0 h]

theorem leadingCoeff_pow' (f : LaurentSeries K) (n : ℕ) :
    (f ^ n).leadingCoeff = f.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, pow_succ]

theorem coeff_jqModC_of_lt {n : ℤ} (hn : n < -1) : (jqModC K).coeff n = 0 := by
  have h := ModularCurve.coeff_jqModC_pow_of_lt K (b := 1) (m := n) (by simpa using hn)
  rwa [pow_one] at h

theorem jqModC_ne_zero' : jqModC K ≠ 0 := by
  intro h
  have h1 := ModularCurve.coeff_jqModC_neg_one K
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

theorem order_jqModC' : (jqModC K).order = -1 :=
  order_eq_of_coeff (by rw [ModularCurve.coeff_jqModC_neg_one]; exact one_ne_zero)
    (fun k hk => coeff_jqModC_of_lt hk)

theorem leadingCoeff_jqModC : (jqModC K).leadingCoeff = 1 := by
  rw [leadingCoeff_eq_coeff (n := -1) (by rw [ModularCurve.coeff_jqModC_neg_one]; exact one_ne_zero)
    (fun k hk => coeff_jqModC_of_lt hk), ModularCurve.coeff_jqModC_neg_one]

theorem thetaJ_coeff_neg_one : (thetaL K (jqModC K)).coeff (-1) = -1 := by
  rw [thetaL_coeff, ModularCurve.coeff_jqModC_neg_one]; simp

theorem thetaJ_coeff_of_lt {k : ℤ} (hk : k < -1) : (thetaL K (jqModC K)).coeff k = 0 := by
  rw [thetaL_coeff, coeff_jqModC_of_lt hk, mul_zero]

theorem thetaJ_ne_zero : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h1 := thetaJ_coeff_neg_one (K := K)
  rw [h, HahnSeries.coeff_zero] at h1
  norm_num at h1

theorem order_thetaJ : (thetaL K (jqModC K)).order = -1 :=
  order_eq_of_coeff (by rw [thetaJ_coeff_neg_one]; norm_num) (fun k hk => thetaJ_coeff_of_lt hk)

theorem leadingCoeff_thetaJ : (thetaL K (jqModC K)).leadingCoeff = -1 := by
  rw [leadingCoeff_eq_coeff (n := -1) (by rw [thetaJ_coeff_neg_one]; norm_num)
    (fun k hk => thetaJ_coeff_of_lt hk), thetaJ_coeff_neg_one]

theorem jsub_coeff_neg_one : (jqModC K - 1728).coeff (-1) = 1 := by
  rw [HahnSeries.coeff_sub, ModularCurve.coeff_jqModC_neg_one, coeff_ofNat_1728 _ (by norm_num),
    sub_zero]

theorem jsub_coeff_of_lt {k : ℤ} (hk : k < -1) : (jqModC K - 1728).coeff k = 0 := by
  rw [HahnSeries.coeff_sub, coeff_jqModC_of_lt hk, coeff_ofNat_1728 _ (by omega), sub_zero]

theorem jsub_ne_zero : jqModC K - 1728 ≠ 0 := by
  intro h
  have h1 := jsub_coeff_neg_one (K := K)
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

theorem order_jsub : (jqModC K - 1728).order = -1 :=
  order_eq_of_coeff (by rw [jsub_coeff_neg_one]; exact one_ne_zero) (fun k hk => jsub_coeff_of_lt hk)

theorem leadingCoeff_jsub : (jqModC K - 1728).leadingCoeff = 1 := by
  rw [leadingCoeff_eq_coeff (n := -1) (by rw [jsub_coeff_neg_one]; exact one_ne_zero)
    (fun k hk => jsub_coeff_of_lt hk), jsub_coeff_neg_one]

theorem coeff_aeval_jqModC (S : Polynomial K) (n : ℤ) :
    (aeval (jqModC K) S).coeff n =
      ∑ i ∈ Finset.range (S.natDegree + 1), S.coeff i * ((jqModC K) ^ i).coeff n := by
  rw [aeval_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

theorem coeff_aeval_jqModC_of_lt (S : Polynomial K) {n : ℤ} (hn : n < -(S.natDegree : ℤ)) :
    (aeval (jqModC K) S).coeff n = 0 := by
  rw [coeff_aeval_jqModC]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [ModularCurve.coeff_jqModC_pow_of_lt K (by omega), mul_zero]

theorem coeff_aeval_jqModC_self (S : Polynomial K) :
    (aeval (jqModC K) S).coeff (-(S.natDegree : ℤ)) = S.leadingCoeff := by
  rw [coeff_aeval_jqModC, Finset.sum_eq_single_of_mem S.natDegree
    (Finset.mem_range.mpr (Nat.lt_succ_self _))]
  · rw [ModularCurve.coeff_jqModC_pow_self, mul_one]; rfl
  · intro i hi hne
    rw [Finset.mem_range] at hi
    rw [ModularCurve.coeff_jqModC_pow_of_lt K (by omega), mul_zero]

theorem order_aeval_jqModC {S : Polynomial K} (hS : S ≠ 0) :
    (aeval (jqModC K) S).order = -(S.natDegree : ℤ) :=
  order_eq_of_coeff (by rw [coeff_aeval_jqModC_self]; exact leadingCoeff_ne_zero.mpr hS)
    (fun k hk => coeff_aeval_jqModC_of_lt S hk)

theorem leadingCoeff_aeval_jqModC {S : Polynomial K} (hS : S ≠ 0) :
    (aeval (jqModC K) S).leadingCoeff = S.leadingCoeff := by
  rw [leadingCoeff_eq_coeff (n := -(S.natDegree : ℤ))
    (by rw [coeff_aeval_jqModC_self]; exact leadingCoeff_ne_zero.mpr hS)
    (fun k hk => coeff_aeval_jqModC_of_lt S hk), coeff_aeval_jqModC_self]

theorem aeval_jqModC_ne_zero {S : Polynomial K} (hS : S ≠ 0) : aeval (jqModC K) S ≠ 0 := by
  intro h
  have h1 := coeff_aeval_jqModC_self (K := K) S
  rw [h, HahnSeries.coeff_zero] at h1
  exact leadingCoeff_ne_zero.mpr hS h1.symm

theorem aeval_jqModC_injective : Function.Injective (aeval (R := K) (jqModC K)) :=
  transcendental_iff_injective.mp (ModularCurve.transcendental_jqModC K)

end Tools

section BaseChange

variable {K k : Type*} [Field K] [Field k] [Algebra K k]

abbrev ιh (K k : Type*) [Field K] [Field k] [Algebra K k] : LaurentSeries K →+* LaurentSeries k :=
  coeffMap (algebraMap K k)

theorem ιh_coeff (x : LaurentSeries K) (n : ℤ) : (ιh K k x).coeff n = algebraMap K k (x.coeff n) :=
  rfl

theorem ιh_injective : Function.Injective (ιh K k) := by
  intro x y h
  ext n
  exact (algebraMap K k).injective (by rw [← ιh_coeff, ← ιh_coeff, h])

theorem ιh_jqModC : ιh K k (jqModC K) = jqModC k := map_jqModC (algebraMap K k)

theorem ιh_thetaL (x : LaurentSeries K) : ιh K k (thetaL K x) = thetaL k (ιh K k x) := by
  ext n
  rw [ιh_coeff, thetaL_coeff, thetaL_coeff, ιh_coeff, map_mul, map_intCast]

theorem ιh_single (n : ℤ) (c : K) :
    ιh K k (HahnSeries.single n c) = HahnSeries.single n (algebraMap K k c) :=
  coeffMap_single _ _ _

theorem ιh_algebraMap (c : K) :
    ιh K k (algebraMap K (LaurentSeries K) c) = algebraMap k (LaurentSeries k) (algebraMap K k c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, ιh_single]

theorem ιh_aeval (S : Polynomial K) (x : LaurentSeries K) :
    ιh K k (aeval x S) = aeval (ιh K k x) (S.map (algebraMap K k)) := by
  refine Polynomial.map_aeval_eq_aeval_map ?_ S x
  ext c
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [ιh_algebraMap]

theorem ιh_ofNat (n : ℕ) [n.AtLeastTwo] :
    ιh K k (OfNat.ofNat n : LaurentSeries K) = OfNat.ofNat n := map_ofNat _ n

end BaseChange

section Retraction

variable {K k : Type*} [Field K] [Field k] [Algebra K k] (π₀ : k →ₗ[K] K)

def πh (y : LaurentSeries k) : LaurentSeries K := y.map π₀

theorem πh_coeff (y : LaurentSeries k) (n : ℤ) : (πh π₀ y).coeff n = π₀ (y.coeff n) := rfl

theorem πh_add (y z : LaurentSeries k) : πh π₀ (y + z) = πh π₀ y + πh π₀ z := by
  ext n; simp only [πh_coeff, HahnSeries.coeff_add, map_add]

theorem πh_sum {α : Type*} (s : Finset α) (f : α → LaurentSeries k) :
    πh π₀ (∑ a ∈ s, f a) = ∑ a ∈ s, πh π₀ (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext n; simp only [Finset.sum_empty, πh_coeff, HahnSeries.coeff_zero, map_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, πh_add, ih]

theorem πh_ιh_mul (f : LaurentSeries K) (y : LaurentSeries k) :
    πh π₀ (ιh K k f * y) = f * πh π₀ y := by
  ext n
  have hsub1 : (ιh K k f).support ⊆ f.support := by
    intro i hi
    rw [HahnSeries.mem_support] at hi ⊢
    intro h0; apply hi; rw [ιh_coeff, h0, map_zero]
  have hsub2 : (πh π₀ y).support ⊆ y.support := by
    intro i hi
    rw [HahnSeries.mem_support] at hi ⊢
    intro h0; apply hi; rw [πh_coeff, h0, map_zero]
  rw [πh_coeff, HahnSeries.coeff_mul_left' f.isPWO_support hsub1,
    HahnSeries.coeff_mul_right' y.isPWO_support hsub2, map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [ιh_coeff, πh_coeff, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem πh_single (n : ℤ) (c : k) : πh π₀ (HahnSeries.single n c) = HahnSeries.single n (π₀ c) := by
  ext m
  rw [πh_coeff]
  rcases eq_or_ne m n with rfl | hm
  · rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
  · rw [HahnSeries.coeff_single_of_ne hm, HahnSeries.coeff_single_of_ne hm, map_zero]

variable (hπ₀ : ∀ c : K, π₀ (algebraMap K k c) = c)
include hπ₀

theorem πh_ιh (f : LaurentSeries K) : πh π₀ (ιh K k f) = f := by
  have h := πh_ιh_mul π₀ f 1
  rw [mul_one] at h
  rw [h, show (1 : LaurentSeries k) = HahnSeries.single 0 1 from rfl, πh_single,
    show (1 : k) = algebraMap K k 1 from (map_one _).symm, hπ₀, HahnSeries.single_zero_one, mul_one]

def descPoly (Pk : Polynomial k) : Polynomial K :=
  ∑ i ∈ Finset.range (Pk.natDegree + 1), C (π₀ (Pk.coeff i)) * X ^ i

omit hπ₀ in
theorem coeff_descPoly (Pk : Polynomial k) (i : ℕ) : (descPoly π₀ Pk).coeff i = π₀ (Pk.coeff i) := by
  rw [descPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (Pk.natDegree + 1)) i (fun j => π₀ (Pk.coeff j))]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

omit hπ₀ in
theorem natDegree_descPoly_le (Pk : Polynomial k) : (descPoly π₀ Pk).natDegree ≤ Pk.natDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  rw [coeff_descPoly, Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero]

omit hπ₀ in
theorem πh_aeval (Pk : Polynomial k) :
    πh π₀ (aeval (jqModC k) Pk) = aeval (jqModC K) (descPoly π₀ Pk) := by
  rw [aeval_eq_sum_range, πh_sum, descPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ιh_jqModC (K := K), ← map_pow, Algebra.smul_def, algebraMap_laurentSeries_eq_single, mul_comm,
    πh_ιh_mul, πh_single, map_mul, map_pow, aeval_X, aeval_C, algebraMap_laurentSeries_eq_single]
  ring

theorem descend (f g : LaurentSeries K) (Pk : Polynomial k)
    (h : ιh K k f * aeval (jqModC k) Pk = ιh K k g) :
    f * aeval (jqModC K) (descPoly π₀ Pk) = g := by
  have h1 := congrArg (πh π₀) h
  rwa [πh_ιh_mul, πh_aeval, πh_ιh π₀ hπ₀] at h1

end Retraction

theorem numerology (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ m e₄ e₆ : ℕ, 12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := hp.eq_one_or_self_of_dvd 2 h; omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := hp.eq_one_or_self_of_dvd 3 h; omega
  refine ⟨(p - 1) / 12, if p % 3 = 2 then 1 else 0, if p % 4 = 3 then 1 else 0, ?_, ?_, ?_⟩
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega

section AlgClosed

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]
include hp5

theorem exists_prod_algClosed (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = p - 1)
    (he₄ : e₄ ≤ 1) (he₆ : e₆ ≤ 1) :
    ∃ Pk : Polynomial k, Pk.Monic ∧ Pk.Separable ∧ Pk.eval 0 ≠ 0 ∧ Pk.eval 1728 ≠ 0 ∧
      thetaL k (jqModC k) ^ (p - 1) * (aeval (jqModC k) Pk) ^ 2 =
        jqModC k ^ (8 * m + 2 * e₄ + 4 * e₆) * (jqModC k - 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) := by
  classical
  set S₀ : Finset k := (ModularCurve.ssJSet_finite p k).toFinset with hS₀def
  have hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet p k := fun a => Set.Finite.mem_toFinset _
  have hmain := ModularCurve.thetaL_jqModC_pow_mul_prod_sq_eq p hp5 m e₄ e₆ hm (by omega) he₆ k S₀ hS₀
  refine ⟨∏ a ∈ S₀ \ {0, 1728}, (X - C a), monic_prod_X_sub_C _ _, ?_, ?_, ?_, ?_⟩
  · exact separable_prod_X_sub_C_iff'.mpr fun x _ y _ h => h
  · rw [eval_prod, Finset.prod_ne_zero_iff]
    intro a ha
    rw [eval_sub, eval_X, eval_C, zero_sub, neg_ne_zero]
    rintro rfl
    simp at ha
  · rw [eval_prod, Finset.prod_ne_zero_iff]
    intro a ha
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    rintro rfl
    simp at ha
  · rw [← hmain, map_prod]
    congr 2
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_sub, aeval_X, aeval_C, algebraMap_laurentSeries_eq_single]
    rfl

end AlgClosed

section Main

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type*) [Field K] [CharP K p]
include hp5

theorem main :
    ∃ (m e₄ e₆ : ℕ) (S : Polynomial K),
      12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      S.Monic ∧ S.Separable ∧ S.natDegree = m ∧ S.eval 0 ≠ 0 ∧ S.eval 1728 ≠ 0 ∧
      thetaL K (jqModC K) ^ ((p - 1) / 2) * aeval (jqModC K) S =
        (-1) ^ ((p - 1) / 2) *
          (jqModC K ^ (4 * m + e₄ + 2 * e₆) * (jqModC K - 1728) ^ (3 * m + e₄ + e₆)) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨m, e₄, e₆, hm, he₄, he₆⟩ := numerology p hp hp5

  have hp2 : ¬ 2 ∣ p := fun h => by have := hp.eq_one_or_self_of_dvd 2 h; omega
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ, s = (p - 1) / 2 := ⟨_, rfl⟩
  have hs2 : p - 1 = 2 * s := by omega
  have hs : s = 6 * m + 2 * e₄ + 3 * e₆ := by omega
  rw [← hsdef]

  let k := AlgebraicClosure K
  haveI : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  obtain ⟨Pk, hPkmonic, hPksep, hPk0, hPk1728, hPk⟩ := exists_prod_algClosed p hp5 k m e₄ e₆ hm he₄ he₆

  set Tk : LaurentSeries k := thetaL k (jqModC k) with hTk
  set Jk : LaurentSeries k := jqModC k with hJk
  set T : LaurentSeries K := thetaL K (jqModC K) with hT
  set J : LaurentSeries K := jqModC K with hJ
  set R : LaurentSeries K := J ^ (4 * m + e₄ + 2 * e₆) * (J - 1728) ^ (3 * m + e₄ + e₆) with hR
  have hιJ : ιh K k J = Jk := ιh_jqModC
  have hι_T : ιh K k T = Tk := by
    show ιh K k (thetaL K (jqModC K)) = thetaL k (jqModC k)
    rw [ιh_thetaL, ιh_jqModC]
  have hιR : ιh K k R = Jk ^ (4 * m + e₄ + 2 * e₆) * (Jk - 1728) ^ (3 * m + e₄ + e₆) := by
    rw [hR, map_mul, map_pow, map_pow, map_sub, hιJ, ιh_ofNat]

  have hsq : (Tk ^ s * aeval Jk Pk) ^ 2 = (ιh K k R) ^ 2 := by
    rw [hιR, mul_pow, ← pow_mul, mul_comm s 2, ← hs2, hPk]; ring
  obtain ⟨σ, hσ, hk⟩ : ∃ σ : LaurentSeries K, (σ = 1 ∨ σ = -1) ∧
      Tk ^ s * aeval Jk Pk = ιh K k (σ * R) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, Or.inl rfl, by rw [one_mul, h]⟩
    · exact ⟨-1, Or.inr rfl, by rw [neg_one_mul, map_neg, h]⟩

  obtain ⟨π₀, hπ₀'⟩ := (Algebra.linearMap K k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K k).injective)
  have hπ₀ : ∀ c : K, π₀ (algebraMap K k c) = c := fun c => by
    have := LinearMap.congr_fun hπ₀' c
    simpa using this

  set S : Polynomial K := descPoly π₀ Pk with hSdef
  have hTS : T ^ s * aeval J S = σ * R :=
    descend π₀ hπ₀ (T ^ s) (σ * R) Pk (by rw [map_pow, hι_T, hk])

  have hT0 : T ≠ 0 := thetaJ_ne_zero
  have hTk0 : Tk ≠ 0 := thetaJ_ne_zero
  have hJ0 : J ≠ 0 := jqModC_ne_zero'
  have hJ' : J - 1728 ≠ 0 := jsub_ne_zero
  have hR0 : R ≠ 0 := mul_ne_zero (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ')
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hσR : σ * R ≠ 0 := mul_ne_zero hσ0 hR0
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at hTS
    exact hσR hTS.symm
  have hA0 : aeval J S ≠ 0 := aeval_jqModC_ne_zero hS0

  have hoJ : J.order = -1 := order_jqModC'
  have hoJ' : (J - 1728).order = -1 := order_jsub
  have hoT : T.order = -1 := order_thetaJ
  have hoA : (aeval J S).order = -(S.natDegree : ℤ) := order_aeval_jqModC hS0
  have hlJ : J.leadingCoeff = 1 := leadingCoeff_jqModC
  have hlJ' : (J - 1728).leadingCoeff = 1 := leadingCoeff_jsub
  have hlT : T.leadingCoeff = -1 := leadingCoeff_thetaJ
  have hlA : (aeval J S).leadingCoeff = S.leadingCoeff := leadingCoeff_aeval_jqModC hS0

  have hordσ : (σ * R).order = R.order := by
    rcases hσ with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, HahnSeries.order_neg]
  have hordR : R.order = -((4 * m + e₄ + 2 * e₆ : ℕ) : ℤ) - ((3 * m + e₄ + e₆ : ℕ) : ℤ) := by
    rw [hR, HahnSeries.order_mul (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ'), HahnSeries.order_pow,
      HahnSeries.order_pow, hoJ, hoJ']
    simp only [nsmul_eq_mul, mul_neg, mul_one]
    ring
  have hordL : (T ^ s * aeval J S).order = -(s : ℤ) - (S.natDegree : ℤ) := by
    rw [HahnSeries.order_mul (pow_ne_zero _ hT0) hA0, HahnSeries.order_pow, hoT, hoA]
    simp only [nsmul_eq_mul, mul_neg, mul_one]
    ring
  have hdeg : S.natDegree = m := by
    have h := congrArg HahnSeries.order hTS
    rw [hordL, hordσ, hordR] at h
    push_cast at h
    omega

  have hSmonic : S.Monic := by
    have hle : S.natDegree ≤ Pk.natDegree := natDegree_descPoly_le π₀ Pk
    have htop : S.coeff Pk.natDegree = 1 := by
      rw [hSdef, coeff_descPoly, Polynomial.Monic.coeff_natDegree hPkmonic,
        show (1 : k) = algebraMap K k 1 from (map_one _).symm, hπ₀]
    exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hle htop

  have hσeq : σ = (-1) ^ s := by
    have h := congrArg HahnSeries.leadingCoeff hTS
    rw [HahnSeries.leadingCoeff_mul, leadingCoeff_pow', hlT, hlA, hSmonic.leadingCoeff, mul_one] at h
    have hlcR : R.leadingCoeff = 1 := by
      rw [hR, HahnSeries.leadingCoeff_mul, leadingCoeff_pow', leadingCoeff_pow', hlJ, hlJ', one_pow,
        one_pow, mul_one]
    have hL1 : (-1 : LaurentSeries K) = algebraMap K (LaurentSeries K) (-1) := by
      rw [map_neg, map_one]
    rcases hσ with rfl | rfl
    · rw [one_mul, hlcR] at h
      rw [hL1, ← map_pow, h, map_one]
    · rw [neg_one_mul, HahnSeries.leadingCoeff_neg, hlcR] at h
      rw [hL1, ← map_pow, h, map_neg, map_one]

  have hmapS : S.map (algebraMap K k) = Pk := by
    apply aeval_jqModC_injective
    have h1 := congrArg (ιh K k) hTS
    rw [map_mul, map_pow, hι_T, ιh_aeval, hιJ, ← hk] at h1
    exact mul_left_cancel₀ (pow_ne_zero _ hTk0) h1
  have hSsep : S.Separable := (Polynomial.separable_map (algebraMap K k)).mp (hmapS ▸ hPksep)
  have hS0' : S.eval 0 ≠ 0 := by
    intro h0; apply hPk0; rw [← hmapS, eval_zero_map, h0, map_zero]
  have hS1728 : S.eval 1728 ≠ 0 := by
    intro h0; apply hPk1728
    rw [← hmapS, show (1728 : k) = algebraMap K k 1728 from (map_ofNat _ _).symm, eval_map,
      eval₂_hom, h0, map_zero]
  refine ⟨m, e₄, e₆, S, hm, he₄, he₆, hSmonic, hSsep, hdeg, hS0', hS1728, ?_⟩
  rw [← hσeq]
  exact hTS

end Main

end AKATZSSH

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (K : Type*) [Field K] [CharP K p] :
    ∃ (m e₄ e₆ : ℕ) (S : Polynomial K),
      12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      S.Monic ∧ S.Separable ∧ S.natDegree = m ∧ S.eval 0 ≠ 0 ∧ S.eval 1728 ≠ 0 ∧
      ModularCurve.thetaL K (ModularCurve.jqModC K) ^ ((p - 1) / 2) *
          Polynomial.aeval (ModularCurve.jqModC K) S =
        (-1) ^ ((p - 1) / 2) *
          (ModularCurve.jqModC K ^ (4 * m + e₄ + 2 * e₆) *
            (ModularCurve.jqModC K - 1728) ^ (3 * m + e₄ + e₆)) :=
  AKATZSSH.main p hp K

end S_ModularCurve_exists_separable_thetaL_jqModC_pow_mul_aeval_eq
end P2MW
export P2MW.S_ModularCurve_exists_separable_thetaL_jqModC_pow_mul_aeval_eq (solution)
