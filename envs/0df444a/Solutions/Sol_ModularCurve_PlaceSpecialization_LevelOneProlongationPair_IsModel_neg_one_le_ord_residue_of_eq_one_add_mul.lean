-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.neg_one_le_ord_residue_of_eq_one_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a3ee4d5d-ad7d-5397-a23d-a42abd5a44d7

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing
import Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_ord_jFun_sub_eq_one_of_isStrictTypeOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_residue_eq_zero_or_le_ord_residue_of_tExpansion_red_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_integers_residue_jFun_sub_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_algebraMap_mem_smoothLocalRingFst
import Theorems.Thm_PowerSeries_mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_neg_one_le_ord_residue_of_eq_one_add_mul
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace Ws25
namespace A3L

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization PowerSeries

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar (1 * q)
local notation "Fb" => modularFunctionFieldC k 1
local notation "cst" => algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
local notation "jF" => PlaceSpecialization.jFun (q := q)

section Helpers
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap' {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hc' : algebraMap K F c ≠ 0 := (_root_.map_ne_zero (algebraMap K F)).mpr hc
  have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ hc'),
      Subtype.ext (by simpa using inv_mul_cancel₀ hc')⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem ord_pow' (x : F) (n : ℕ) : v.ord (x ^ n) = n * v.ord x := by
  rw [← zpow_natCast, v.ord_zpow]

theorem min_ord_le_ord_add {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (v.ord x) (v.ord y) ≤ v.ord (x + y) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπF : (π : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  set m := min (v.ord x) (v.ord y) with hm
  have hmem : ∀ z : F, z ≠ 0 → m ≤ v.ord z → z * (π : F) ^ (-m) ∈ v.toValuationSubring := by
    intro z hz hmz
    rw [v.mem_iff_ord_nonneg (mul_ne_zero hz (zpow_ne_zero _ hπF)), v.ord_mul hz (zpow_ne_zero _ hπF),
      v.ord_zpow, v.ord_coe_irreducible hπ, mul_one]
    omega
  have hsum : (x + y) * (π : F) ^ (-m) ∈ v.toValuationSubring := by
    rw [add_mul]; exact add_mem (hmem x hx (min_le_left _ _)) (hmem y hy (min_le_right _ _))
  have h := v.ord_nonneg_of_mem hsum
  rw [v.ord_mul hxy (zpow_ne_zero _ hπF), v.ord_zpow, v.ord_coe_irreducible hπ, mul_one] at h
  omega

theorem ord_neg (x : F) : v.ord (-x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h : (-x) = algebraMap K F (-1) * x := by simp
    rw [h, v.ord_mul ((_root_.map_ne_zero _).mpr (by norm_num)) hx, ord_algebraMap' v (by norm_num), zero_add]

theorem ord_add_eq_of_lt {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hlt : v.ord x < v.ord y) :
    v.ord (x + y) = v.ord x := by
  have hxy : x + y ≠ 0 := by
    intro h
    have : x = -y := eq_neg_of_add_eq_zero_left h
    rw [this, ord_neg] at hlt; exact lt_irrefl _ hlt
  have h1 := min_ord_le_ord_add v hx hy hxy
  have h2 := min_ord_le_ord_add v hxy (neg_ne_zero.mpr hy) (by simpa using hx)
  rw [ord_neg, add_neg_cancel_right] at h2
  omega

theorem inv_mem_of_isUnit {S : ValuationSubring F} {x : F} (hx : x ∈ S) (hu : IsUnit (⟨x, hx⟩ : S)) :
    x⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : S) : F) = x := by rw [hu]
  have hx0 : x ≠ 0 := by rw [← hcoe]; simp
  have h1 : x * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  have : (((u⁻¹ : Sˣ) : S) : F) = x⁻¹ := (eq_inv_of_mul_eq_one_right h1)
  rw [← this]; exact SetLike.coe_mem _

end Helpers

set_option maxHeartbeats 6400000 in
theorem main (hR : R.IsModel)
    {Q Q' : Place QQ FF}
    (hQ : P.IsStrictTypeOne Q) (hQ' : P.IsStrictTypeOne Q') (hQQ' : P.redFst Q' = P.redFst Q) (hne : Q' ≠ Q)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (g : FF) (hg₁ : g ∈ R.R₁.integers) (hg₁' : R.R₁.residue ⟨g, hg₁⟩ ≠ 0)
    (hgQ : Q.ord g = -(n : ℤ)) (hgQ' : Q'.ord g = n)
    (hg0 : ∀ W : Place QQ FF, P.IsStrictTypeOne W → P.redFst W = P.redFst Q → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : A) (ε : FF) (hε₁ : ε ∈ R.R₁.integers) (hε₁' : R.R₁.residue ⟨ε, hε₁⟩ ≠ 0)
    (hgε : g = 1 + cst (e : QQ) * ε) :
    -1 ≤ (P.redFst Q).ord (R.residue₁ ⟨ε, hε₁⟩) := by
  classical

  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have hnA : IsUnit ((n : ℕ) : A) := by
    have hred : red (n : A) ≠ 0 := by rwa [map_natCast]
    rw [show red (n : A) = R.redBar (IsLocalRing.residue A n) from (R.redBar_residue _).symm] at hred
    have : IsLocalRing.residue A n ≠ 0 := fun h0 => hred (by rw [h0, map_zero])
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp this
  have hg0' : g ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hgQ
    have : (n : ℤ) = 0 := by omega
    exact hn0 (by exact_mod_cast this)
  have he0 : e ≠ 0 := by
    rintro rfl
    have : g = 1 := by rw [hgε]; simp
    rw [this, Place.ord_one] at hgQ
    have : (n : ℤ) = 0 := by omega
    exact hn0 (by exact_mod_cast this)
  have he0' : (e : QQ) ≠ 0 := by simpa using he0

  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : A, 0 < Q.ord (jF - cst (j₀ : QQ)) := by
    by_contra h; push Not at h; exact (ModularCurve.not_isStrictType_of_isCuspidal P Q h).1 hQ
  obtain ⟨j₀', hj₀'⟩ : ∃ j₀' : A, 0 < Q'.ord (jF - cst (j₀' : QQ)) := by
    by_contra h; push Not at h; exact (ModularCurve.not_isStrictType_of_isCuspidal P Q' h).1 hQ'

  obtain ⟨φ, hrem, hX, hC⟩ := hR.exists_ringHom_tExpansion hQ j₀ hj₀
  obtain ⟨htQ, ht0⟩ := hR.ord_jFun_sub_eq_one_of_isStrictTypeOne hQ j₀ hj₀
  obtain ⟨ht'Q', ht'0⟩ := hR.ord_jFun_sub_eq_one_of_isStrictTypeOne hQ' j₀' hj₀'
  obtain ⟨ht₁, htres⟩ := R.exists_mem_integers_residue_jFun_sub_ne_zero j₀
  obtain ⟨ht'₁, ht'res⟩ := R.exists_mem_integers_residue_jFun_sub_ne_zero j₀'
  have hordt := R.ord_redFst_residue_jFun_sub_eq_one (Q := Q) j₀ hj₀ ht₁
  set t : FF := jF - cst (j₀ : QQ) with ht_def
  set t' : FF := jF - cst (j₀' : QQ) with ht'_def
  set a : A := j₀' - j₀ with ha_def
  have ht't : t' = t - cst (a : QQ) := by
    simp only [ht_def, ht'_def, ha_def, AddSubgroupClass.coe_sub, map_sub]; ring

  have hreda : red a = 0 := by
    have h1 := (ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff P Q (red j₀)).mpr ⟨j₀, rfl, hj₀⟩
    have h2 := (ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff P Q' (red j₀')).mpr ⟨j₀', rfl, hj₀'⟩
    rw [hQQ', h1] at h2
    have := charLGeomPlaceOfPoint_injective k h2
    rw [ha_def, map_sub, this, sub_self]
  have haM : a ∈ IsLocalRing.maximalIdeal A := by
    have h := R.redBar_residue a
    rw [hreda] at h
    have : IsLocalRing.residue A a = 0 := R.redBar.injective (by rw [h, map_zero])
    exact (IsLocalRing.residue_eq_zero_iff a).mp this

  have htQ' : Q'.ord t = 0 := ht0 Q' hQ' hQQ' hne
  have ht'Q : Q.ord t' = 0 := ht'0 Q hQ hQQ'.symm (Ne.symm hne)
  have ht0' : t ≠ 0 := by intro h; rw [h, Place.ord_zero] at htQ; exact zero_ne_one htQ
  have ht'0' : t' ≠ 0 := by intro h; rw [h, Place.ord_zero] at ht'Q'; exact zero_ne_one ht'Q'

  have ht'u : IsUnit (⟨t', ht'₁⟩ : R.R₁.integers) := R.R₁.isUnit_of_residue_ne_zero ht'res
  have ht'inv : t'⁻¹ ∈ R.R₁.integers := inv_mem_of_isUnit ht'₁ ht'u
  have ht'invu : IsUnit (⟨t'⁻¹, ht'inv⟩ : R.R₁.integers) :=
    isUnit_iff_exists_inv.mpr ⟨⟨t', ht'₁⟩, Subtype.ext (inv_mul_cancel₀ ht'0')⟩

  set u : FF := g * t ^ n * t'⁻¹ ^ n with hu_def
  have hu₁ : u ∈ R.R₁.integers := mul_mem (mul_mem hg₁ (pow_mem ht₁ n)) (pow_mem ht'inv n)
  have hures : R.R₁.residue ⟨u, hu₁⟩ ≠ 0 := by
    have : (⟨u, hu₁⟩ : R.R₁.integers) = ⟨g, hg₁⟩ * ⟨t, ht₁⟩ ^ n * ⟨t'⁻¹, ht'inv⟩ ^ n :=
      Subtype.ext (by simp [hu_def])
    rw [this, map_mul, map_mul, map_pow, map_pow]
    exact mul_ne_zero (mul_ne_zero hg₁' (pow_ne_zero _ htres))
      (pow_ne_zero _ (R.R₁.residue_ne_zero_of_isUnit ht'invu))
  have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero hg0' (pow_ne_zero _ ht0')) (pow_ne_zero _ (inv_ne_zero ht'0'))
  have hordu : ∀ W : Place QQ FF, P.IsStrictTypeOne W → P.redFst W = P.redFst Q → W.ord u = 0 := by
    intro W hW hWv
    rw [hu_def, W.ord_mul (mul_ne_zero hg0' (pow_ne_zero _ ht0')) (pow_ne_zero _ (inv_ne_zero ht'0')),
      W.ord_mul hg0' (pow_ne_zero _ ht0'), ord_pow', ord_pow', W.ord_inv]
    by_cases hWQ : W = Q
    · subst hWQ; rw [hgQ, htQ, ht'Q]; ring
    by_cases hWQ' : W = Q'
    · subst hWQ'; rw [hgQ', htQ', ht'Q']; ring
    rw [hg0 W hW hWv hWQ hWQ', ht0 W hW hWv hWQ, ht'0 W hW (hWv.trans hQQ'.symm) hWQ']; ring
  obtain ⟨hu𝒪, huinv𝒪⟩ :=
    R.mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero (P.redFst Q) ⟨Q, hQ, rfl⟩ u hu₁ hures hordu

  have ht𝒪 : t ∈ R.smoothLocalRingFst (P.redFst Q) := by
    refine (R.mem_smoothLocalRingFst_iff (P.redFst Q) t).mpr ⟨ht₁, fun W hW hWv => ?_⟩
    refine W.mem_of_ord_nonneg ht0' ?_
    by_cases hWQ : W = Q
    · subst hWQ; rw [htQ]; exact zero_le_one
    · rw [ht0 W hW hWv hWQ]
  have ha𝒪 := R.algebraMap_mem_smoothLocalRingFst (P.redFst Q) a
  have he𝒪 := R.algebraMap_mem_smoothLocalRingFst (P.redFst Q) e
  have ht'𝒪 : t' ∈ R.smoothLocalRingFst (P.redFst Q) := by rw [ht't]; exact sub_mem ht𝒪 ha𝒪

  have hce : cst (e : QQ) ≠ 0 := (_root_.map_ne_zero _).mpr he0'
  have hε_eq : ε = (cst (e : QQ))⁻¹ * (g - 1) := by
    rw [hgε, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hce]; exact (one_mul ε).symm
  have hg1 : g - 1 ≠ 0 := by
    intro h
    have : ε = 0 := by rw [hε_eq, h, mul_zero]
    apply hε₁'
    have h0 : (⟨ε, hε₁⟩ : R.R₁.integers) = 0 := Subtype.ext this
    rw [h0, map_zero]
  have hordε : ∀ W : Place QQ FF, W.ord ε = W.ord (g - 1) := by
    intro W
    rw [hε_eq, W.ord_mul (inv_ne_zero ((_root_.map_ne_zero _).mpr he0')) hg1, W.ord_inv,
      ord_algebraMap' W he0', neg_zero, zero_add]
  have hε0 : ε ≠ 0 := by rw [hε_eq]; exact mul_ne_zero (inv_ne_zero ((_root_.map_ne_zero _).mpr he0')) hg1
  set y : FF := ε * t ^ n with hy_def
  have hy₁ : y ∈ R.R₁.integers := mul_mem hε₁ (pow_mem ht₁ n)
  have hy𝒪 : y ∈ R.smoothLocalRingFst (P.redFst Q) := by
    refine (R.mem_smoothLocalRingFst_iff (P.redFst Q) y).mpr ⟨hy₁, fun W hW hWv => ?_⟩
    refine W.mem_of_ord_nonneg (mul_ne_zero hε0 (pow_ne_zero _ ht0')) ?_
    rw [hy_def, W.ord_mul hε0 (pow_ne_zero _ ht0'), ord_pow', hordε]
    by_cases hWQ : W = Q
    · subst hWQ
      rw [htQ, sub_eq_add_neg, ord_add_eq_of_lt W hg0' (by norm_num) (by
        rw [ord_neg, Place.ord_one, hgQ]; have : (0:ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        omega), hgQ]
      ring_nf; exact le_rfl
    · have hg_nn : 0 ≤ W.ord g := by
        by_cases hWQ' : W = Q'
        · subst hWQ'; rw [hgQ']; exact_mod_cast Nat.zero_le n
        · rw [hg0 W hW hWv hWQ hWQ']
      have : 0 ≤ W.ord (g - 1) :=
        W.ord_nonneg_of_mem (sub_mem (W.mem_of_ord_nonneg hg0' hg_nn) (one_mem _))
      rw [ht0 W hW hWv hWQ, mul_zero, add_zero]; exact this

  have hidF : u * t' ^ n = t ^ n + cst (e : QQ) * y := by
    have h1 : t'⁻¹ ^ n * t' ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ ht'0', one_pow]
    calc u * t' ^ n = g * t ^ n * (t'⁻¹ ^ n * t' ^ n) := by rw [hu_def]; ring
      _ = g * t ^ n := by rw [h1, mul_one]
      _ = t ^ n + cst (e : QQ) * y := by rw [hgε, hy_def]; ring
  have hid𝒪 : (⟨u, hu𝒪⟩ : R.smoothLocalRingFst (P.redFst Q)) * ⟨t', ht'𝒪⟩ ^ n
      = ⟨t, ht𝒪⟩ ^ n + ⟨cst (e : QQ), he𝒪⟩ * ⟨y, hy𝒪⟩ := Subtype.ext (by simpa using hidF)
  have hφt : φ ⟨t, ht𝒪⟩ = X := hX ht𝒪
  have hφt' : φ ⟨t', ht'𝒪⟩ = X - C a := by
    have : (⟨t', ht'𝒪⟩ : R.smoothLocalRingFst (P.redFst Q)) = ⟨t, ht𝒪⟩ - ⟨cst (a : QQ), ha𝒪⟩ := Subtype.ext ht't
    rw [this, map_sub, hφt, hC a ha𝒪]
  have hidX : φ ⟨u, hu𝒪⟩ * (X - C a) ^ n = X ^ n + C e * φ ⟨y, hy𝒪⟩ := by
    have := congrArg φ hid𝒪
    rw [map_mul, map_pow, map_add, map_mul, map_pow, hφt', hφt, hC e he𝒪] at this
    exact this
  have hUunit : IsUnit (constantCoeff (φ ⟨u, hu𝒪⟩)) := by
    rw [← isUnit_iff_constantCoeff]
    refine isUnit_iff_exists_inv.mpr ⟨φ ⟨u⁻¹, huinv𝒪⟩, ?_⟩
    rw [← map_mul, ← map_one φ]
    congr 1
    exact Subtype.ext (mul_inv_cancel₀ hu0)

  have hspan : ∀ i < n, coeff i (φ ⟨u, hu𝒪⟩ * (X - C a) ^ n - X ^ n) ∈ Ideal.span {e} := by
    intro i _
    rw [hidX, add_sub_cancel_left, coeff_C_mul]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right e _)
  obtain ⟨-, hcoef⟩ := PowerSeries.mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span n hnA (φ ⟨u, hu𝒪⟩) hUunit a haM e hspan
  have hred : ∀ i < n - 1, red (coeff i (φ ⟨y, hy𝒪⟩)) = 0 := by
    intro i hi
    have h := hcoef i (by omega)
    rw [hidX, add_sub_cancel_left, coeff_C_mul] at h
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h
    have : coeff i (φ ⟨y, hy𝒪⟩) = s * a := by
      have h' : e * (coeff i (φ ⟨y, hy𝒪⟩) - s * a) = 0 := by rw [mul_sub, ← hs]; ring
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' he0
      · exact sub_eq_zero.mp h''
    rw [this, map_mul, hreda, mul_zero]

  have hγ := hR.residue_eq_zero_or_le_ord_residue_of_tExpansion_red_eq_zero hQ j₀ hj₀ y hy₁ hy𝒪
    (fun i => coeff i (φ ⟨y, hy𝒪⟩)) (n - 1) (hrem ⟨y, hy𝒪⟩ (n - 1)) hred

  have hresy : R.residue₁ ⟨y, hy₁⟩ = R.residue₁ ⟨ε, hε₁⟩ * R.residue₁ ⟨t, ht₁⟩ ^ n := by
    have : (⟨y, hy₁⟩ : R.R₁.integers) = ⟨ε, hε₁⟩ * ⟨t, ht₁⟩ ^ n := Subtype.ext (by simp [hy_def])
    rw [this, map_mul, map_pow]
  have hrest : R.residue₁ ⟨t, ht₁⟩ ≠ 0 := by
    rw [R.residue₁_apply]; exact (map_ne_zero_iff R.ι R.ι.injective).mpr htres
  have hresε : R.residue₁ ⟨ε, hε₁⟩ ≠ 0 := by
    rw [R.residue₁_apply]; exact (map_ne_zero_iff R.ι R.ι.injective).mpr hε₁'
  rcases hγ with h0 | hle
  · exfalso
    rw [hresy] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hresε h
    · exact hrest (pow_eq_zero_iff hn0 |>.mp h)
  · rw [hresy, (P.redFst Q).ord_mul hresε (pow_ne_zero _ hrest), ord_pow', hordt, mul_one] at hle
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0)]; simp
    rw [hcast] at hle
    omega

end Ws25.A3L

end

open AlgebraicCurve IsLocalRing ModularCurve in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.LevelOneProlongationPair} (hR : R.IsModel)
    {Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hQ : P.IsStrictTypeOne Q) (hQ' : P.IsStrictTypeOne Q') (hQQ' : P.redFst Q' = P.redFst Q) (hne : Q' ≠ Q)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg₁ : g ∈ R.R₁.integers) (hg₁' : R.R₁.residue ⟨g, hg₁⟩ ≠ 0)
    (hgQ : Q.ord g = -(n : ℤ)) (hgQ' : Q'.ord g = n)
    (hg0 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictTypeOne W → P.redFst W = P.redFst Q → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : A) (ε : ↥(modularFunctionFieldBar (1 * q))) (hε₁ : ε ∈ R.R₁.integers) (hε₁' : R.R₁.residue ⟨ε, hε₁⟩ ≠ 0)
    (hgε : g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (e : AlgebraicClosure ℚ) * ε) :
    -1 ≤ (P.redFst Q).ord (R.residue₁ ⟨ε, hε₁⟩) :=
  Ws25.A3L.main R hR hQ hQ' hQQ' hne n hn g hg₁ hg₁' hgQ hgQ' hg0 e ε hε₁ hε₁' hgε

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_neg_one_le_ord_residue_of_eq_one_add_mul
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_neg_one_le_ord_residue_of_eq_one_add_mul (solution)
