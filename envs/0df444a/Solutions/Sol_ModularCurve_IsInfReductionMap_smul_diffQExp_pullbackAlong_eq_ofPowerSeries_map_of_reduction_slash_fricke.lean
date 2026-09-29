-- Prove2me | solution 1 for ModularCurve.IsInfReductionMap.smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/1aa2d9ef-facc-5d51-bb21-f1769f1d6ab3

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_TateFormal
import Theorems.Thm_CuspForm_exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularForm_eisenstein_qCoeff_p_integral_dvd
import Theorems.Thm_ModularCurve_thetaL_qExpand
import Theorems.Thm_ModularCurve_thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsInfReductionMap_smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped MatrixGroups ModularForm Pointwise TensorProduct
open UpperHalfPlane HahnSeries CongruenceSubgroup CohCarrier

namespace FrickeReadB

section Series

variable (K : Type*) [Field K]

set_option synthInstance.maxHeartbeats 1600000 in
scoped instance instModuleLaurentShortcut : Module K (LaurentSeries K) := inferInstance

theorem thetaL_coeff (x : LaurentSeries K) (n : ℤ) :
    (ModularCurve.thetaL K x).coeff n = (n : K) * x.coeff n := by
  show (single (1 : ℤ) (1 : K) * LaurentSeries.derivative K x).coeff n = _
  rw [HahnSeries.coeff_single_mul, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    Nat.cast_one, sub_add_cancel, Ring.choose_one_right, one_mul, zsmul_eq_mul]

theorem thetaL_eq_qEuler (x : LaurentSeries K) : ModularCurve.thetaL K x = ModularCurve.qEuler K x := by
  ext n
  rw [thetaL_coeff, ModularCurve.qEuler_coeff]

def expandPS {R : Type*} [CommRing R] (N : ℕ) (P : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => if N ∣ n then PowerSeries.coeff (n / N) P else 0

theorem coeff_expandPS {R : Type*} [CommRing R] (N : ℕ) (P : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (expandPS N P) = if N ∣ n then PowerSeries.coeff (n / N) P else 0 := by
  rw [expandPS, PowerSeries.coeff_mk]

theorem map_expandPS {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (N : ℕ) (P : PowerSeries R) :
    (expandPS N P).map g = expandPS N (P.map g) := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_expandPS]
  split_ifs <;> simp

theorem ofPowerSeries_expandPS {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (P : PowerSeries R) :
    ofPowerSeries ℤ R (expandPS N P) = ModularCurve.qExpand R N (ofPowerSeries ℤ R P) := by
  ext m
  by_cases hm : (N : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [ModularCurve.qExpand_coeff_mul]
    by_cases hk : 0 ≤ k
    · lift k to ℕ using hk
      rw [show ((N : ℤ) * (k : ℤ)) = ((N * k : ℕ) : ℤ) by push_cast; ring, ofPowerSeries_apply_coeff,
        ofPowerSeries_apply_coeff, coeff_expandPS, if_pos (Dvd.intro k rfl),
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N))]
    · push Not at hk
      have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      have hNk : (N : ℤ) * k < 0 := mul_neg_of_pos_of_neg hN hk
      rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hNk, ModularCurve.ofPowerSeries_coeff_of_neg _ hk]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd N _ hm]
    by_cases hm0 : 0 ≤ m
    · lift m to ℕ using hm0
      rw [ofPowerSeries_apply_coeff, coeff_expandPS, if_neg]
      intro h
      exact hm (by exact_mod_cast h)
    · push Not at hm0
      rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hm0]

theorem ofPowerSeries_map_map_intCast {S : Type*} [CommRing S] (φ : S →+* K) (P : PowerSeries ℤ) :
    ofPowerSeries ℤ K ((P.map (Int.castRingHom S)).map φ) = ModularCurve.intSeriesC K P := by
  unfold ModularCurve.intSeriesC
  congr 1
  ext n
  simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]

theorem intSeriesC_C_mul (c : ℤ) (P : PowerSeries ℤ) :
    ModularCurve.intSeriesC K (PowerSeries.C c * P) = HahnSeries.C (c : K) * ModularCurve.intSeriesC K P := by
  rw [ModularCurve.intSeriesC_mul]
  congr 1
  rw [ModularCurve.intSeriesC, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C]

theorem intSeriesC_expandPS (N : ℕ) [NeZero N] (P : PowerSeries ℤ) :
    ModularCurve.intSeriesC K (expandPS N P) = ModularCurve.qExpand K N (ModularCurve.intSeriesC K P) := by
  rw [ModularCurve.intSeriesC, map_expandPS, ofPowerSeries_expandPS]
  rfl

theorem intSeriesC_eq_smul_of_dvd (p : ℕ) [CharP K p] (P pf : PowerSeries ℤ) (D₁ : ℤ)
    (h : ∀ n : ℕ, (p : ℤ) ∣ PowerSeries.coeff n P - D₁ * PowerSeries.coeff n pf) :
    ModularCurve.intSeriesC K P = HahnSeries.C (D₁ : K) * ModularCurve.intSeriesC K pf := by
  rw [← intSeriesC_C_mul]
  unfold ModularCurve.intSeriesC
  congr 1
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_C_mul, eq_intCast, eq_intCast]
  obtain ⟨c, hc⟩ := h n
  have : (PowerSeries.coeff n P : ℤ) = D₁ * PowerSeries.coeff n pf + p * c := by linarith
  rw [this]
  push_cast
  simp

theorem intSeriesC_ne_zero_of_coeff (P : PowerSeries ℤ) (n : ℕ) (h : ((PowerSeries.coeff n P : ℤ) : K) ≠ 0) :
    ModularCurve.intSeriesC K P ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun x : LaurentSeries K => x.coeff (n : ℤ)) h0
  simp only [HahnSeries.coeff_zero] at this
  rw [← this, ModularCurve.intSeriesC, ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast]

end Series

section LevelOne

theorem coe_le_SL (Γ : Subgroup SL(2, ℤ)) : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
  rw [MonoidHom.range_eq_map]
  exact Subgroup.map_mono le_top

theorem one_mem_strictPeriods_SL : (1 : ℝ) ∈ Subgroup.strictPeriods 𝒮ℒ := by
  rw [Subgroup.strictPeriods_SL2Z]
  exact AddSubgroup.mem_zmultiples 1

theorem one_mem_strictPeriods_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ Subgroup.strictPeriods (Γ : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

def E4 : ModularForm 𝒮ℒ ((4 : ℕ) : ℤ) := ModularForm.E (show 3 ≤ 4 by norm_num)

def E6 : ModularForm 𝒮ℒ ((6 : ℕ) : ℤ) := ModularForm.E (show 3 ≤ 6 by norm_num)

def Del : ModularForm 𝒮ℒ 12 := (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

@[scoped simp] theorem coe_Del : (⇑Del : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

theorem bernoulli'_five : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, bernoulli'_five, Nat.choose]

theorem isIntegralQExp_E4 : ModularCurve.IsIntegralQExp ⇑E4 ModularCurve.eisenstein4 := by
  rw [ModularCurve.isIntegralQExp_iff]
  intro n
  rw [E4, EisensteinSeries.E_qExpansion_coeff (show 3 ≤ 4 by norm_num) (by decide) n, ModularCurve.eisenstein4,
    PowerSeries.coeff_mk, bernoulli_four, ArithmeticFunction.sigma_apply]
  split_ifs
  · simp
  · push_cast
    ring

theorem isIntegralQExp_E6 : ModularCurve.IsIntegralQExp ⇑E6 ModularCurve.eisenstein6 := by
  rw [ModularCurve.isIntegralQExp_iff]
  intro n
  rw [E6, EisensteinSeries.E_qExpansion_coeff (show 3 ≤ 6 by norm_num) (by decide) n, ModularCurve.eisenstein6,
    PowerSeries.coeff_mk, bernoulli_six, ArithmeticFunction.sigma_apply]
  split_ifs
  · simp
  · push_cast
    ring

def pDel : PowerSeries ℤ := PowerSeries.X * ModularCurve.dedekindEtaUnit

theorem isIntegralQExp_Del : ModularCurve.IsIntegralQExp ⇑Del pDel :=
  ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

attribute [irreducible] E4 E6 Del

theorem coeff_one_pDel : PowerSeries.coeff 1 pDel = 1 := by
  rw [pDel, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff,
    ModularCurve.constantCoeff_dedekindEtaUnit]

variable {Γ : Subgroup (GL (Fin 2) ℝ)}

theorem isIntegralQExp_mul (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {a b : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b)
    {pf pg : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp ⇑f pf) (hg : ModularCurve.IsIntegralQExp ⇑g pg) :
    ModularCurve.IsIntegralQExp (⇑f * ⇑g) (pf * pg) := by
  unfold ModularCurve.IsIntegralQExp at *
  rw [map_mul, hf, hg, ModularForm.qExpansion_mul_coe one_pos hΓ f g]

theorem isIntegralQExp_add (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {a : ℤ} (f g : ModularForm Γ a)
    {pf pg : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp ⇑f pf) (hg : ModularCurve.IsIntegralQExp ⇑g pg) :
    ModularCurve.IsIntegralQExp ⇑(f + g) (pf + pg) := by
  unfold ModularCurve.IsIntegralQExp at *
  rw [map_add, hf, hg, ModularForm.coe_add, ModularForm.qExpansion_add one_pos hΓ f g]

theorem isIntegralQExp_natCast_smul [Γ.HasDetOne] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {a : ℤ} (f : ModularForm Γ a)
    {pf : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp ⇑f pf) (c : ℤ) :
    ModularCurve.IsIntegralQExp ⇑((c : ℂ) • f) (PowerSeries.C c * pf) := by
  unfold ModularCurve.IsIntegralQExp at *
  rw [map_mul, hf, PowerSeries.map_C, eq_intCast, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos hΓ (c : ℂ) f, PowerSeries.smul_eq_C_mul, map_intCast]

theorem exists_hasseLift (p : ℕ) [Fact p.Prime] (w : ℕ) (hw0 : 0 < w) (hwp : p - 1 ∣ w) (hw4 : 4 ∣ w) :
    ∃ (s : ℕ) (x : ℤ) (Ew : ModularForm 𝒮ℒ (w : ℤ)) (pEw : PowerSeries ℤ),
      ¬ p ∣ s ∧ (p : ℤ) ∣ x ∧ ModularCurve.IsIntegralQExp ⇑Ew pEw ∧
      pEw = PowerSeries.mk (fun n => if n = 0 then (s : ℤ) else x * ((ArithmeticFunction.sigma (w - 1) n : ℕ) : ℤ)) := by
  have hw3 : 3 ≤ w := by
    obtain ⟨c, rfl⟩ := hw4
    omega
  have hw2 : Even w := by
    obtain ⟨c, rfl⟩ := hw4
    exact ⟨2 * c, by ring⟩
  obtain ⟨x, s, hps, hx, hpx⟩ := ModularForm.eisenstein_qCoeff_p_integral_dvd p hw3 hw2 hwp 1 one_pos
  refine ⟨s, x, ((s : ℤ) : ℂ) • ModularForm.E hw3, _, hps, hpx, ?_, rfl⟩
  rw [ModularCurve.isIntegralQExp_iff]
  intro n
  rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL _ (ModularForm.E hw3),
    PowerSeries.coeff_smul, EisensteinSeries.E_qExpansion_coeff hw3 hw2 n, PowerSeries.coeff_mk]
  rw [EisensteinSeries.E_qExpansion_coeff hw3 hw2 1, if_neg one_ne_zero, ArithmeticFunction.sigma_one] at hx
  split_ifs
  · simp
  · push_cast
    rw [hx]
    push_cast
    ring

theorem intSeriesC_hasseLift (K : Type*) [Field K] (p : ℕ) [CharP K p] (w : ℕ) (s : ℕ) (x : ℤ) (hpx : (p : ℤ) ∣ x) :
    ModularCurve.intSeriesC K
        (PowerSeries.mk (fun n => if n = 0 then (s : ℤ) else x * ((ArithmeticFunction.sigma (w - 1) n : ℕ) : ℤ))) =
      HahnSeries.C (s : K) := by
  rw [← HahnSeries.ofPowerSeries_C, ModularCurve.intSeriesC]
  congr 1
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_C, eq_intCast]
  obtain ⟨c, rfl⟩ := hpx
  split_ifs
  · simp
  · push_cast
    simp

end LevelOne

section FrickeMatrix

variable (Q : ℕ) [NeZero Q] (WQ : GL (Fin 2) ℝ)
  (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((Q : ℕ) : ℝ), 0])

include hWQ in
theorem WQ_eq : WQ = Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * ModularForm.heckeDiagMatrix Q := by
  ext i j
  rw [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne Q), hWQ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]

def lowerUnip : SL(2, ℤ) := ⟨!![1, 0; -(Q : ℤ), 1], by simp [Matrix.det_fin_two_of]⟩

include hWQ in
theorem WQ_mul_T : WQ * Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T =
    Matrix.SpecialLinearGroup.mapGL ℝ (lowerUnip Q) * WQ := by
  ext i j
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hWQ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_T, lowerUnip, Matrix.mul_apply, Fin.sum_univ_two]

include hWQ in
theorem one_mem_strictPeriods_conj {Γ : Subgroup SL(2, ℤ)} (hL : lowerUnip Q ∈ Γ) :
    (1 : ℝ) ∈ (ConjAct.toConjAct WQ⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv,
    ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
  have hT : Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T := by
    ext i j
    rw [Matrix.GeneralLinearGroup.upperRightHom_apply]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_T]
  rw [hT, WQ_mul_T Q WQ hWQ, mul_inv_cancel_right]
  exact ⟨lowerUnip Q, hL, rfl⟩

include hWQ in

theorem analyticAt_cuspFunction_smul_slash_WQ {Γ : Subgroup SL(2, ℤ)} (hL : lowerUnip Q ∈ Γ) {k : ℤ}
    (F : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (c : ℂ) :
    AnalyticAt ℂ (cuspFunction 1 (c • ((⇑F : ℍ → ℂ) ∣[k] WQ))) 0 := by
  have hper := one_mem_strictPeriods_conj Q WQ hWQ hL
  have han : AnalyticAt ℂ (cuspFunction 1 ((⇑F : ℍ → ℂ) ∣[k] WQ)) 0 := by
    rw [← ModularForm.coe_translate]
    exact ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.translate F WQ) one_pos hper
  rw [cuspFunction_smul han.continuousAt]
  exact analyticAt_const.smul han

include hWQ in
theorem slash_WQ_levelOne {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ((⇑F : ℍ → ℂ) ∣[k] WQ) = fun τ => (Q : ℂ) ^ (k - 1) * F (ModularForm.heckeDiagMatrix Q • τ) := by
  rw [WQ_eq Q WQ hWQ, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq F _ (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩)]
  ext τ
  rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne Q)]

theorem qParam_heckeDiagMatrix_smul (τ : ℍ) :
    Function.Periodic.qParam 1 ((ModularForm.heckeDiagMatrix Q • τ : ℍ) : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) ^ Q := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne Q),
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem lowerUnip_mem_top : lowerUnip Q ∈ (⊤ : Subgroup SL(2, ℤ)) := Subgroup.mem_top _

include hWQ in

theorem qExpansion_smul_slash_WQ_levelOne {k : ℤ} (F : ModularForm 𝒮ℒ k) (m : ℕ) (hm : k - 1 = m)
    (P : PowerSeries ℤ) (hP : ModularCurve.IsIntegralQExp ⇑F P) (c : ℕ) :
    (PowerSeries.C (((c * Q ^ m : ℕ) : ℤ)) * expandPS Q P).map (Int.castRingHom ℂ) =
      qExpansion 1 ((c : ℂ) • ((⇑F : ℍ → ℂ) ∣[k] WQ)) := by
  have hSL : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) = ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    MonoidHom.range_eq_map (Matrix.SpecialLinearGroup.mapGL ℝ)
  have hper : (1 : ℝ) ∈ (ConjAct.toConjAct WQ⁻¹ • (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [hSL]; exact one_mem_strictPeriods_conj Q WQ hWQ (lowerUnip_mem_top Q)

  set Fc : ModularForm (ConjAct.toConjAct WQ⁻¹ • (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) k :=
    ModularForm.translate ((c : ℂ) • F) WQ with hFc
  have hcoe : (⇑Fc : ℍ → ℂ) = (c : ℂ) • ((⇑F : ℍ → ℂ) ∣[k] WQ) := by
    rw [hFc, ModularForm.coe_translate, ModularForm.IsGLPos.coe_smul, ModularForm.smul_slash]
    have hσ : (UpperHalfPlane.σ WQ) (c : ℂ) = c := by
      rw [← Complex.ofReal_natCast, UpperHalfPlane.σ_ofReal]
    rw [hσ]
  have h1 : (1 : ℝ) ∈ Subgroup.strictPeriods 𝒮ℒ := by
    rw [Subgroup.strictPeriods_SL2Z]; exact AddSubgroup.mem_zmultiples 1
  haveI : Fact (IsCusp OnePoint.infty (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  have hsum : ∀ τ : ℍ, HasSum (fun n : ℕ =>
      (if Q ∣ n then (c : ℂ) * (Q : ℂ) ^ m * (qExpansion 1 ⇑F).coeff (n / Q) else 0) • Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (Fc τ) := by
    intro τ
    have hF := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex F h1)
      (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) (ModularForm.heckeDiagMatrix Q • τ)
    rw [qParam_heckeDiagMatrix_smul Q] at hF
    have hF2 := hF.mul_left ((c : ℂ) * (Q : ℂ) ^ m)
    have hval : Fc τ = (c : ℂ) * (Q : ℂ) ^ m * F (ModularForm.heckeDiagMatrix Q • τ) := by
      rw [hcoe, Pi.smul_apply, slash_WQ_levelOne Q WQ hWQ F, smul_eq_mul, hm, zpow_natCast]
      ring
    rw [hval]
    have hinj : Function.Injective (fun n : ℕ => Q * n) := mul_right_injective₀ (NeZero.ne Q)
    refine (Function.Injective.hasSum_iff hinj ?_).mp ?_
    · intro n hn
      have : ¬ Q ∣ n := by
        rintro ⟨d, rfl⟩
        exact hn ⟨d, rfl⟩
      simp [this]
    · convert hF2 using 1
      all_goals first
        | rfl
        | (ext n
           simp only [Function.comp_apply, if_pos (Dvd.intro n rfl),
             Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne Q)), smul_eq_mul, pow_mul]
           ring)
  rw [← hcoe]
  refine PowerSeries.ext fun n => ?_
  rw [← ModularFormClass.qExpansion_coeff_unique one_pos hper hsum n, PowerSeries.coeff_map, PowerSeries.coeff_C_mul,
    coeff_expandPS, eq_intCast]
  split_ifs with h
  · rw [← hP.coeff (n / Q)]
    push_cast
    ring
  · push_cast
    simp

end FrickeMatrix

section Spec

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
  (K : Type*) [Field K] (φ : ↥(integralClosure ℤ ℂ) →+* K) (WQ : GL (Fin 2) ℝ)

def FrickeSpec
    (σ : ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ≃ₐ[K]
      ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
    ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
    PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQ)) →
    PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQ)) →
    ModularCurve.intSeriesC K pg ≠ 0 →
    ofPowerSeries ℤ K (PgW.map φ) ≠ 0 →
    ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
      (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
      ((σ x : ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) :
          LaurentSeries K) * ofPowerSeries ℤ K (PgW.map φ) = ofPowerSeries ℤ K (PfW.map φ)

variable {p M H hpM K φ WQ}

theorem T_mem_GammaH (N : ℕ) (H' : Subgroup (ZMod N)ˣ) : ModularGroup.T ∈ GammaH N H' := by
  rw [mem_GammaH_iff]
  have hT : ModularGroup.T ∈ Gamma0 N := by simp [ModularGroup.T]
  refine ⟨hT, ?_⟩
  have : gamma0Units N ⟨ModularGroup.T, hT⟩ = 1 := by
    ext
    rw [val_gamma0Units, Units.val_one]
    show (((ModularGroup.T : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = 1
    simp [ModularGroup.T]
  rw [this]
  exact one_mem H'

theorem lowerUnip_mem_GammaH (N : ℕ) (H' : Subgroup (ZMod N)ˣ) : lowerUnip N ∈ GammaH N H' := by
  rw [mem_GammaH_iff]
  have h0 : lowerUnip N ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show (((-(N : ℤ)) : ℤ) : ZMod N) = 0
    simp
  refine ⟨h0, ?_⟩
  have : gamma0Units N ⟨lowerUnip N, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units, Units.val_one]
    show ((((lowerUnip N) : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = 1
    simp [lowerUnip]
  rw [this]
  exact one_mem H'

theorem map_map_algebraMap (P : PowerSeries ℤ) :
    ((P.map (Int.castRingHom ↥(integralClosure ℤ ℂ))).map (algebraMap ↥(integralClosure ℤ ℂ) ℂ)) =
      P.map (Int.castRingHom ℂ) := by
  ext n
  simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]

def pE43 : PowerSeries ℤ := ModularCurve.eisenstein4 * ModularCurve.eisenstein4 * ModularCurve.eisenstein4

theorem jqModC_mul_intSeriesC_pDel (K : Type*) [Field K] :
    ModularCurve.jqModC K * ModularCurve.intSeriesC K pDel = ModularCurve.intSeriesC K pE43 := by
  have h1 : ofPowerSeries ℤ K (ModularCurve.dedekindEtaUnitInv.map (Int.castRingHom K)) *
      ofPowerSeries ℤ K (ModularCurve.dedekindEtaUnit.map (Int.castRingHom K)) = 1 := by
    rw [← map_mul, ← map_mul, mul_comm, ModularCurve.dedekindEtaUnit_mul_inv, map_one, map_one]
  have hs : single (-1 : ℤ) (1 : K) * single (1 : ℤ) (1 : K) = 1 := by
    rw [HahnSeries.single_mul_single, neg_add_cancel, one_mul]; rfl
  have h3 : ModularCurve.jNum = pE43 * ModularCurve.dedekindEtaUnitInv := by
    rw [ModularCurve.jNum, pE43, pow_three']
  rw [ModularCurve.jqModC, h3, pDel, ModularCurve.intSeriesC, ModularCurve.intSeriesC, map_mul, map_mul, map_mul,
    map_mul, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  calc _ = (single (-1 : ℤ) (1 : K) * single (1 : ℤ) (1 : K)) *
          ofPowerSeries ℤ K (pE43.map (Int.castRingHom K)) *
          (ofPowerSeries ℤ K (ModularCurve.dedekindEtaUnitInv.map (Int.castRingHom K)) *
            ofPowerSeries ℤ K (ModularCurve.dedekindEtaUnit.map (Int.castRingHom K))) := by ring
    _ = _ := by rw [hs, h1, one_mul, mul_one]

theorem intSeriesC_pDel_ne_zero (K : Type*) [Field K] : ModularCurve.intSeriesC K pDel ≠ 0 :=
  intSeriesC_ne_zero_of_coeff K pDel 1 (by rw [coeff_one_pDel]; simp)

theorem twelve_eq : (12 : ℤ) = ((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ) := by norm_num

def formE43 (Γ : Subgroup SL(2, ℤ)) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ)) :=
  ModularCurve.restrictForm (coe_le_SL Γ) ((E4.mul E4).mul E4)

def formDel (Γ : Subgroup SL(2, ℤ)) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ)) :=
  ModularCurve.restrictForm (coe_le_SL Γ) (ModularForm.mcast twelve_eq Del)

theorem isIntegralQExp_congr {f g : ℍ → ℂ} (hfg : f = g) {P : PowerSeries ℤ} (h : ModularCurve.IsIntegralQExp g P) :
    ModularCurve.IsIntegralQExp f P := hfg ▸ h

theorem isIntegralQExp_mul' {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {a b : ℤ}
    (f : ModularForm Γ a) (g : ModularForm Γ b)
    {pf pg : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp ⇑f pf) (hg : ModularCurve.IsIntegralQExp ⇑g pg) :
    ModularCurve.IsIntegralQExp ⇑(f.mul g) (pf * pg) :=
  isIntegralQExp_congr (ModularForm.coe_mul f g) (isIntegralQExp_mul hΓ f g hf hg)

theorem isIntegralQExp_E43 : ModularCurve.IsIntegralQExp (⇑((E4.mul E4).mul E4)) pE43 :=
  isIntegralQExp_mul' one_mem_strictPeriods_SL (E4.mul E4) E4
    (isIntegralQExp_mul' one_mem_strictPeriods_SL E4 E4 isIntegralQExp_E4 isIntegralQExp_E4) isIntegralQExp_E4

theorem isIntegralQExp_mcast_Del : ModularCurve.IsIntegralQExp (⇑(ModularForm.mcast twelve_eq Del)) pDel :=
  isIntegralQExp_Del

def wData (Q c m : ℕ) (P : PowerSeries ℤ) : PowerSeries ↥(integralClosure ℤ ℂ) :=
  (PowerSeries.C (((c * Q ^ m : ℕ) : ℤ)) * expandPS Q P).map (Int.castRingHom ↥(integralClosure ℤ ℂ))

theorem wData_map_algebraMap (Q c m : ℕ) (P : PowerSeries ℤ) :
    (wData Q c m P).map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      (PowerSeries.C (((c * Q ^ m : ℕ) : ℤ)) * expandPS Q P).map (Int.castRingHom ℂ) :=
  map_map_algebraMap _

theorem ofPowerSeries_wData_map (K : Type*) [Field K] (φ : ↥(integralClosure ℤ ℂ) →+* K) (Q c m : ℕ) [NeZero Q]
    (P : PowerSeries ℤ) :
    ofPowerSeries ℤ K ((wData Q c m P).map φ) =
      HahnSeries.C ((c : K) * (Q : K) ^ m) * ModularCurve.qExpand K Q (ModularCurve.intSeriesC K P) := by
  rw [wData, ofPowerSeries_map_map_intCast, intSeriesC_C_mul, intSeriesC_expandPS]
  push_cast
  ring

variable (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])

include hWQ in

theorem coe_sigma_j (hQ : ((M / p : ℕ) : K) ≠ 0)
    (σ : ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ≃ₐ[K]
      ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
    (hσ : FrickeSpec p M H hpM K φ WQ σ)
    (hj : ModularCurve.jqModC K ∈ ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :
    ((σ ⟨ModularCurve.jqModC K, hj⟩ :
        ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) =
      ModularCurve.qExpand K (M / p) (ModularCurve.jqModC K) := by
  have hpf : ModularCurve.IsIntegralQExp ⇑(formE43 (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
      pE43 := isIntegralQExp_E43
  have hpg : ModularCurve.IsIntegralQExp ⇑(formDel (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) pDel :=
    isIntegralQExp_mcast_Del
  have hPfW : (wData (M / p) 1 11 pE43).map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      qExpansion 1 (((1 : ℕ) : ℂ) • ((⇑(formE43 (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : ℍ → ℂ)
        ∣[((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ)] WQ)) := by
    rw [wData_map_algebraMap]
    exact qExpansion_smul_slash_WQ_levelOne (M / p) WQ hWQ ((E4.mul E4).mul E4) 11 (by norm_num) _ isIntegralQExp_E43 1
  have hPgW : (wData (M / p) 1 11 pDel).map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      qExpansion 1 (((1 : ℕ) : ℂ) • ((⇑(formDel (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : ℍ → ℂ)
        ∣[((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ)] WQ)) := by
    rw [wData_map_algebraMap]
    exact qExpansion_smul_slash_WQ_levelOne (M / p) WQ hWQ (ModularForm.mcast twelve_eq Del) 11 (by norm_num) _
      isIntegralQExp_mcast_Del 1
  have hg0 : ModularCurve.intSeriesC K pDel ≠ 0 := intSeriesC_pDel_ne_zero K
  have hqinj : Function.Injective (ModularCurve.qExpand K (M / p)) := ModularCurve.qExpand_injective (M / p)
  have hne : HahnSeries.C (((1 : ℕ) : K) * ((M / p : ℕ) : K) ^ 11) *
      ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K pDel) ≠ 0 := by
    refine mul_ne_zero ?_ ((map_ne_zero_iff _ hqinj).mpr hg0)
    rw [Nat.cast_one, one_mul]
    exact HahnSeries.C_ne_zero (pow_ne_zero _ hQ)
  have hPgW0 : ofPowerSeries ℤ K ((wData (M / p) 1 11 pDel).map φ) ≠ 0 := by
    rw [ofPowerSeries_wData_map]
    exact hne
  have hx : ((⟨ModularCurve.jqModC K, hj⟩ :
      ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) =
      ModularCurve.intSeriesC K pE43 / ModularCurve.intSeriesC K pDel := by
    rw [eq_div_iff hg0]
    exact jqModC_mul_intSeriesC_pDel K
  have key := hσ _ (formE43 _) (formDel _) _ _ 1 _ _ hpf hpg hPfW hPgW hg0 hPgW0 _ hx
  rw [ofPowerSeries_wData_map, ofPowerSeries_wData_map, ← jqModC_mul_intSeriesC_pDel K,
    map_mul (ModularCurve.qExpand K (M / p))] at key
  apply mul_right_cancel₀ hne
  rw [key]
  ring

end Spec

section SpecB

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {K : Type*} [Field K] {φ : ↥(integralClosure ℤ ℂ) →+* K} {WQ : GL (Fin 2) ℝ}

def pE14w (pEw : PowerSeries ℤ) : PowerSeries ℤ :=
  ModularCurve.eisenstein4 * ModularCurve.eisenstein4 * ModularCurve.eisenstein6 * pEw

theorem weight_eq (w : ℕ) :
    ((4 : ℕ) : ℤ) + ((4 : ℕ) : ℤ) + ((6 : ℕ) : ℤ) + (w : ℤ) = ((2 : ℤ) + w) + 12 := by push_cast; ring

def formHOne (w : ℕ) (Ew : ModularForm 𝒮ℒ (w : ℤ)) : ModularForm 𝒮ℒ (((2 : ℤ) + w) + 12) :=
  ModularForm.mcast (weight_eq w) (((E4.mul E4).mul E6).mul Ew)

theorem isIntegralQExp_formHOne (w : ℕ) (Ew : ModularForm 𝒮ℒ (w : ℤ)) (pEw : PowerSeries ℤ)
    (hEw : ModularCurve.IsIntegralQExp ⇑Ew pEw) :
    ModularCurve.IsIntegralQExp ⇑(formHOne w Ew) (pE14w pEw) :=
  isIntegralQExp_mul' one_mem_strictPeriods_SL ((E4.mul E4).mul E6) Ew
    (isIntegralQExp_mul' one_mem_strictPeriods_SL (E4.mul E4) E6
      (isIntegralQExp_mul' one_mem_strictPeriods_SL E4 E4 isIntegralQExp_E4 isIntegralQExp_E4) isIntegralQExp_E6) hEw

theorem abs_det_WQ (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0]) :
    |((Matrix.GeneralLinearGroup.det WQ : ℝˣ) : ℝ)| = ((M / p : ℕ) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, hWQ, Matrix.det_fin_two_of]
  simp

theorem y_mem (w : ℕ) (G : ModularForm (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) ((2 : ℤ) + w))
    (P : PowerSeries ℤ) (hGP : ModularCurve.IsIntegralQExp ⇑G P)
    (s : ℕ) (hs : (s : K) ≠ 0) (Ew : ModularForm 𝒮ℒ (w : ℤ)) (pEw : PowerSeries ℤ)
    (hEw : ModularCurve.IsIntegralQExp ⇑Ew pEw) (hpEw : ModularCurve.intSeriesC K pEw = HahnSeries.C (s : K)) :
    ModularCurve.intSeriesC K (P * pDel + pE14w pEw) / ModularCurve.intSeriesC K (pE14w pEw) ∈
      ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) := by
  have hle := coe_le_SL (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))
  have hΓ1 : (1 : ℝ) ∈ Subgroup.strictPeriods
      (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) :=
    one_mem_strictPeriods_of_T_mem (T_mem_GammaH _ _)
  let DelR : ModularForm (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) 12 :=
    ModularCurve.restrictForm hle Del
  let N₁ : ModularForm (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ))
      (((2 : ℤ) + w) + 12) := G.mul DelR
  let Hd : ModularForm (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ))
      (((2 : ℤ) + w) + 12) := ModularCurve.restrictForm hle (formHOne w Ew)
  have hN₁ : ModularCurve.IsIntegralQExp ⇑N₁ (P * pDel) := isIntegralQExp_mul' hΓ1 G DelR hGP isIntegralQExp_Del
  have hHdOne : ModularCurve.IsIntegralQExp ⇑(formHOne w Ew) (pE14w pEw) := isIntegralQExp_formHOne w Ew pEw hEw
  have hHd : ModularCurve.IsIntegralQExp ⇑Hd (pE14w pEw) := hHdOne
  have hnum : ModularCurve.IsIntegralQExp ⇑(N₁ + Hd) (P * pDel + pE14w pEw) := isIntegralQExp_add hΓ1 N₁ Hd hN₁ hHd
  have he4 : ModularCurve.intSeriesC K ModularCurve.eisenstein4 ≠ 0 :=
    intSeriesC_ne_zero_of_coeff K _ 0 (by simp [ModularCurve.eisenstein4])
  have he6 : ModularCurve.intSeriesC K ModularCurve.eisenstein6 ≠ 0 :=
    intSeriesC_ne_zero_of_coeff K _ 0 (by simp [ModularCurve.eisenstein6])
  have hden0 : ModularCurve.intSeriesC K (pE14w pEw) ≠ 0 := by
    rw [pE14w, ModularCurve.intSeriesC_mul, ModularCurve.intSeriesC_mul, ModularCurve.intSeriesC_mul, hpEw]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero he4 he4) he6) (HahnSeries.C_ne_zero hs)
  exact ModularCurve.div_mem_qExpFunctionFieldC (N₁ + Hd) Hd hnum hHd hden0

variable (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])

include hWQ in

theorem coe_sigma_y (hQ : ((M / p : ℕ) : K) ≠ 0)
    (σ : ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ≃ₐ[K]
      ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
    (hσ : FrickeSpec p M H hpM K φ WQ σ)
    (w : ℕ) (G : ModularForm (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) ((2 : ℤ) + w))
    (P : PowerSeries ℤ) (hGP : ModularCurve.IsIntegralQExp ⇑G P) (D₂ : ℕ) (hD₂ : (D₂ : K) ≠ 0)
    (PGW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hPGW : PGW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      qExpansion 1 ((D₂ : ℂ) • ((⇑G : ℍ → ℂ) ∣[(2 : ℤ) + w] WQ)))
    (s : ℕ) (hs : (s : K) ≠ 0) (Ew : ModularForm 𝒮ℒ (w : ℤ)) (pEw : PowerSeries ℤ)
    (hEw : ModularCurve.IsIntegralQExp ⇑Ew pEw) (hpEw : ModularCurve.intSeriesC K pEw = HahnSeries.C (s : K))
    (hy : ModularCurve.intSeriesC K (P * pDel + pE14w pEw) / ModularCurve.intSeriesC K (pE14w pEw) ∈
      ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :
    ((σ ⟨_, hy⟩ : ↥(ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) :
        LaurentSeries K) *
        (HahnSeries.C ((D₂ : K) * ((M / p : ℕ) : K) ^ (13 + w)) *
          ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K (pE14w pEw))) =
      ofPowerSeries ℤ K (PGW.map φ) *
          (HahnSeries.C ((((M / p : ℕ) : K)) * ((M / p : ℕ) : K) ^ 11) *
            ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K pDel)) +
        HahnSeries.C ((D₂ : K) * ((M / p : ℕ) : K) ^ (13 + w)) *
          ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K (pE14w pEw)) := by
  have hle := coe_le_SL (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))
  have hΓ1 : (1 : ℝ) ∈ Subgroup.strictPeriods
      (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) :=
    one_mem_strictPeriods_of_T_mem (T_mem_GammaH _ _)
  have hL := lowerUnip_mem_GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)

  let DelR : ModularForm (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) 12 :=
    ModularCurve.restrictForm hle Del
  let N₁ : ModularForm (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ))
      (((2 : ℤ) + w) + 12) := G.mul DelR
  let Hd : ModularForm (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ))
      (((2 : ℤ) + w) + 12) := ModularCurve.restrictForm hle (formHOne w Ew)
  have hN₁ : ModularCurve.IsIntegralQExp ⇑N₁ (P * pDel) := isIntegralQExp_mul' hΓ1 G DelR hGP isIntegralQExp_Del
  have hHdOne : ModularCurve.IsIntegralQExp ⇑(formHOne w Ew) (pE14w pEw) := isIntegralQExp_formHOne w Ew pEw hEw
  have hHd : ModularCurve.IsIntegralQExp ⇑Hd (pE14w pEw) := hHdOne
  have hnum : ModularCurve.IsIntegralQExp ⇑(N₁ + Hd) (P * pDel + pE14w pEw) := isIntegralQExp_add hΓ1 N₁ Hd hN₁ hHd

  have hPgW : (wData (M / p) D₂ (13 + w) (pE14w pEw)).map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      qExpansion 1 ((D₂ : ℂ) • ((⇑Hd : ℍ → ℂ) ∣[((2 : ℤ) + w) + 12] WQ)) := by
    rw [wData_map_algebraMap]
    exact qExpansion_smul_slash_WQ_levelOne (M / p) WQ hWQ (formHOne w Ew) (13 + w) (by push_cast; ring) _ hHdOne D₂

  have hDelW : (wData (M / p) (M / p) 11 pDel).map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      qExpansion 1 ((((M / p : ℕ)) : ℂ) • ((⇑DelR : ℍ → ℂ) ∣[(12 : ℤ)] WQ)) := by
    rw [wData_map_algebraMap]
    exact qExpansion_smul_slash_WQ_levelOne (M / p) WQ hWQ Del 11 (by norm_num) _ isIntegralQExp_Del (M / p)
  have hfun : (D₂ : ℂ) • ((⇑N₁ : ℍ → ℂ) ∣[((2 : ℤ) + w) + 12] WQ) =
      ((D₂ : ℂ) • ((⇑G : ℍ → ℂ) ∣[(2 : ℤ) + w] WQ)) * ((((M / p : ℕ)) : ℂ) • ((⇑DelR : ℍ → ℂ) ∣[(12 : ℤ)] WQ)) := by
    have hcoe : (⇑N₁ : ℍ → ℂ) = ⇑G * ⇑DelR := ModularForm.coe_mul G DelR
    rw [hcoe, ModularForm.mul_slash, abs_det_WQ hWQ]
    funext τ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_natCast]
    ring
  have hN₁W : (PGW * wData (M / p) (M / p) 11 pDel).map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      qExpansion 1 ((D₂ : ℂ) • ((⇑N₁ : ℍ → ℂ) ∣[((2 : ℤ) + w) + 12] WQ)) := by
    rw [map_mul, hPGW, hDelW, hfun]
    exact (qExpansion_mul (analyticAt_cuspFunction_smul_slash_WQ (M / p) WQ hWQ hL G _)
      (analyticAt_cuspFunction_smul_slash_WQ (M / p) WQ hWQ hL DelR _)).symm
  have hPfW : (PGW * wData (M / p) (M / p) 11 pDel + wData (M / p) D₂ (13 + w) (pE14w pEw)).map
        (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      qExpansion 1 ((D₂ : ℂ) • ((⇑(N₁ + Hd) : ℍ → ℂ) ∣[((2 : ℤ) + w) + 12] WQ)) := by
    rw [map_add, hN₁W, hPgW, ModularForm.coe_add, SlashAction.add_slash, smul_add]
    exact (qExpansion_add (analyticAt_cuspFunction_smul_slash_WQ (M / p) WQ hWQ hL N₁ _)
      (analyticAt_cuspFunction_smul_slash_WQ (M / p) WQ hWQ hL Hd _)).symm

  have he4 : ModularCurve.intSeriesC K ModularCurve.eisenstein4 ≠ 0 :=
    intSeriesC_ne_zero_of_coeff K _ 0 (by simp [ModularCurve.eisenstein4])
  have he6 : ModularCurve.intSeriesC K ModularCurve.eisenstein6 ≠ 0 :=
    intSeriesC_ne_zero_of_coeff K _ 0 (by simp [ModularCurve.eisenstein6])
  have hden0 : ModularCurve.intSeriesC K (pE14w pEw) ≠ 0 := by
    rw [pE14w, ModularCurve.intSeriesC_mul, ModularCurve.intSeriesC_mul, ModularCurve.intSeriesC_mul, hpEw]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero he4 he4) he6) (HahnSeries.C_ne_zero hs)
  have hqinj : Function.Injective (ModularCurve.qExpand K (M / p)) := ModularCurve.qExpand_injective (M / p)
  have hPgW0 : ofPowerSeries ℤ K ((wData (M / p) D₂ (13 + w) (pE14w pEw)).map φ) ≠ 0 := by
    rw [ofPowerSeries_wData_map]
    exact mul_ne_zero (HahnSeries.C_ne_zero (mul_ne_zero hD₂ (pow_ne_zero _ hQ))) ((map_ne_zero_iff _ hqinj).mpr hden0)
  have key := hσ _ (N₁ + Hd) Hd _ _ D₂ _ _ hnum hHd hPfW hPgW hden0 hPgW0 ⟨_, hy⟩ rfl
  rw [map_add, map_mul, map_add, map_mul, ofPowerSeries_wData_map, ofPowerSeries_wData_map] at key
  exact key

end SpecB

section Transfer

theorem map_qEuler {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) :
    (ModularCurve.qEuler R x).map f = ModularCurve.qEuler S (x.map f) := by
  ext n
  simp only [HahnSeries.map_coeff, ModularCurve.qEuler_coeff, map_mul, map_intCast]

theorem map_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : PowerSeries R) :
    (ofPowerSeries ℤ R P).map f = ofPowerSeries ℤ S (P.map f) := by
  ext n
  rw [HahnSeries.map_coeff]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · push Not at hn
    rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hn, ModularCurve.ofPowerSeries_coeff_of_neg _ hn, map_zero]

def ramanujanExpr (R : Type*) [CommRing R] : LaurentSeries R :=
  ModularCurve.qEuler R (ModularCurve.jqModC R) * ofPowerSeries ℤ R (ModularCurve.eisenstein4.map (Int.castRingHom R)) +
    ModularCurve.jqModC R * ofPowerSeries ℤ R (ModularCurve.eisenstein6.map (Int.castRingHom R))

theorem rh_map_add {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x y : LaurentSeries R) :
    (x + y).map f = x.map f + y.map f := by
  ext n
  simp [HahnSeries.map_coeff]

theorem rh_map_mul {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x y : LaurentSeries R) :
    (x * y).map f = x.map f * y.map f :=
  HahnSeries.map_mul f.toNonUnitalRingHom

theorem map_ramanujanExpr {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (ramanujanExpr R).map f = ramanujanExpr S := by
  have hmm : ∀ P : PowerSeries ℤ, (P.map (Int.castRingHom R)).map f = P.map (Int.castRingHom S) := by
    intro P
    ext n
    simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]
  rw [ramanujanExpr, ramanujanExpr, rh_map_add, rh_map_mul, rh_map_mul, map_qEuler, ModularCurve.map_jqModC,
    map_ofPowerSeries, map_ofPowerSeries, hmm, hmm]

theorem qEuler_jqModC_mul_e4 (K : Type*) [Field K] :
    ModularCurve.qEuler K (ModularCurve.jqModC K) * ModularCurve.intSeriesC K ModularCurve.eisenstein4 =
      -(ModularCurve.jqModC K * ModularCurve.intSeriesC K ModularCurve.eisenstein6) := by
  have hQ : ramanujanExpr ℚ = 0 := by
    have h := ModularCurve.thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6
    rw [thetaL_eq_qEuler, ← ModularCurve.jqModC_rat] at h
    rw [ramanujanExpr, h]
    ring
  have hZ : ramanujanExpr ℤ = 0 := by
    ext n
    have h1 := congrArg (fun x : LaurentSeries ℚ => x.coeff n) (map_ramanujanExpr (R := ℤ) (Int.castRingHom ℚ))
    simp only [HahnSeries.map_coeff, hQ, HahnSeries.coeff_zero, eq_intCast, Int.cast_eq_zero] at h1
    rw [HahnSeries.coeff_zero]
    exact h1
  have hK : ramanujanExpr K = 0 := by
    rw [← map_ramanujanExpr (Int.castRingHom K), hZ]
    ext n
    simp [HahnSeries.map_coeff]
  rw [ramanujanExpr] at hK
  unfold ModularCurve.intSeriesC
  linear_combination hK

end Transfer

section Frame

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ}

def datumAtP (hp : p.Prime) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : ModularForm.AtkinLehnerDatum M p := by
  have hcop : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    apply hpM2
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    calc M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
      _ = p ^ 2 * c := by rw [hc]; ring
  have hcopZ : IsCoprime (p : ℤ) ((M / p : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  exact
    { R := M / p
      hM := (Nat.mul_div_cancel' hpM).symm
      a := (Classical.choose hcopZ)
      b := -(Classical.choose (Classical.choose_spec hcopZ))
      bezout := by
        have h := Classical.choose_spec (Classical.choose_spec hcopZ)
        linear_combination h }

theorem exists_isIntegralQExp_of_mem (hp : p.Prime) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (f : CuspForm (GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ pf : PowerSeries ℤ, ModularCurve.IsIntegralQExp ⇑f pf := by
  classical
  have h1 : (1 : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2) ∈ CuspForm.heckeRingH M H 2 := Subring.one_mem _
  have hn : ∀ n : ℕ, ∃ m : ℤ, (m : ℂ) = ModularFormClass.qCoeff (⇑f) n := by
    intro n
    have := (hf 1 h1 (datumAtP hp hpM hpM2) n).1
    rw [Module.End.one_apply] at this
    exact Subring.mem_bot.mp this
  refine ⟨PowerSeries.mk fun n => Classical.choose (hn n), ?_⟩
  rw [ModularCurve.isIntegralQExp_iff]
  intro n
  rw [PowerSeries.coeff_mk, Classical.choose_spec (hn n)]
  rfl

end Frame

section Algebra

theorem x0_identity {L : Type*} [Field L] (y a d t E cs cD1 u : L)
    (h5 : y * (E * cs) = cD1 * a * d + E * cs) (hdt : d * t = -E) (hu : cD1 * u = 1) (hE : E * cs ≠ 0) :
    (-(cs * u)) * (y - 1) * t = a := by
  apply mul_right_cancel₀ hE
  linear_combination (-(cs * u * t)) * h5 + (-(cs * u * cD1 * a)) * hdt + (cs * a * E) * hu

theorem final_identity {L : Type*} [Field L] (σy gφ fφ qd qt qE cs cQ cD cD1 cD2 u : L) (w : ℕ)
    (h3 : σy * (cD2 * cQ ^ (13 + w) * (qE * cs)) = gφ * (cQ * cQ ^ 11 * qd) + cD2 * cQ ^ (13 + w) * (qE * cs))
    (h4 : cD * gφ = cD2 * cD1 * cQ ^ w * fφ)
    (hdt : qd * qt = -qE) (hu : cD1 * u = 1)
    (hZ : cD2 * cQ ^ (13 + w) * (qE * cs) ≠ 0) :
    cD * ((-(cs * u)) * (σy - 1) * (cQ * qt)) = fφ := by
  apply mul_right_cancel₀ hZ
  linear_combination (-(cD * cs * u * cQ * qt)) * h3 + (-(cD * cs * u * cQ ^ 13 * gφ)) * hdt +
    (cs * u * cQ ^ 13 * qE) * h4 + (cs * cQ ^ 13 * qE * cD2 * cQ ^ w * fφ) * hu

end Algebra

end FrickeReadB
p2m_reactivate "P2MW.S_ModularCurve_IsInfReductionMap_smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke.FrickeReadB"

open FrickeReadB in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (φ : ↥(integralClosure ℤ ℂ) →+* K)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])
    (σ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
    (hσ : ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQ)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQ)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map φ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((σ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) :
                  LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map φ) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map φ))
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (D : ℕ) (hD : ¬ p ∣ D)
    (pfW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpfW : pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))) :
    (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        (AlgebraicCurve.Differential.pullbackAlong
          σ.toAlgHom
          (ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
            ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩))) =
      HahnSeries.ofPowerSeries ℤ K (pfW.map φ) := by
  classical
  have hp : p.Prime := Fact.out
  have hpQ : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    calc M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
      _ = p ^ 2 * c := by rw [hc]; ring
  have hcast : ∀ n : ℕ, ¬ p ∣ n → ((n : ℕ) : K) ≠ 0 := fun n hn h => hn ((CharP.cast_eq_zero_iff K p n).mp h)
  have hQK : ((M / p : ℕ) : K) ≠ 0 := hcast _ hpQ
  have hDK : ((D : ℕ) : K) ≠ 0 := hcast _ hD
  have hφp : ((p : ℕ) : ↥(integralClosure ℤ ℂ)) ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hker : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ

  obtain ⟨pf, hpf⟩ := exists_isIntegralQExp_of_mem hp hpM hpM2 f hf

  obtain ⟨w, G, P, D₁, D₂, PGW, hw0, hwp, hw4, hD₁, hD₂, hGP, hcong, hPGW, hcongW⟩ :=
    CuspForm.exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet p M H hpM hpM2 hHp
      (RingHom.ker φ) hker hφp Wd e he WQ hWQ f hf pf hpf D hD pfW hpfW
  have hD₁K : ((D₁ : ℕ) : K) ≠ 0 := hcast _ hD₁
  have hD₂K : ((D₂ : ℕ) : K) ≠ 0 := hcast _ hD₂

  obtain ⟨s, x, Ew, pEw, hps, hpx, hEw, hpEw_def⟩ := exists_hasseLift p w hw0 hwp hw4
  have hsK : ((s : ℕ) : K) ≠ 0 := hcast _ hps
  have hpEw : ModularCurve.intSeriesC K pEw = HahnSeries.C (s : K) := by
    rw [hpEw_def]; exact intSeriesC_hasseLift K p w s x hpx

  have hPred : ModularCurve.intSeriesC K P = HahnSeries.C ((D₁ : ℕ) : K) * ModularCurve.intSeriesC K pf := by
    rw [intSeriesC_eq_smul_of_dvd K p P pf (D₁ : ℤ) hcong, Int.cast_natCast]

  have hPGWred : HahnSeries.C ((D : ℕ) : K) * HahnSeries.ofPowerSeries ℤ K (PGW.map φ) =
      HahnSeries.C (((D₂ * D₁ * (M / p) ^ w : ℕ)) : K) * HahnSeries.ofPowerSeries ℤ K (pfW.map φ) := by
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul]
    ext n
    rw [HahnSeries.coeff_smul, HahnSeries.coeff_smul, smul_eq_mul, smul_eq_mul]
    by_cases hn : 0 ≤ n
    · lift n to ℕ using hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
        PowerSeries.coeff_map]
      have h1 := hcongW n
      rw [RingHom.mem_ker, map_sub, map_mul, map_mul, map_natCast, map_natCast, sub_eq_zero] at h1
      exact h1
    · push Not at hn
      rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hn, ModularCurve.ofPowerSeries_coeff_of_neg _ hn, mul_zero, mul_zero]

  have hj : ModularCurve.jqModC K ∈
      ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) :=
    ModularCurve.intFormRatiosC_subset K _ (ModularCurve.jqModC_mem_intFormRatiosC K _)
  have hy := y_mem (hpM := hpM) w G P hGP s hsK Ew pEw hEw hpEw

  have hσj := coe_sigma_j (hpM := hpM) (φ := φ) hWQ hQK σ hσ hj
  have hσy := coe_sigma_y (hpM := hpM) hWQ hQK σ hσ w G P hGP D₂ hD₂K PGW hPGW s hsK Ew pEw hEw hpEw hy

  have hR := qEuler_jqModC_mul_e4 K
  have hjD := jqModC_mul_intSeriesC_pDel K
  rw [pE43, ModularCurve.intSeriesC_mul, ModularCurve.intSeriesC_mul] at hjD
  have he4 : ModularCurve.intSeriesC K ModularCurve.eisenstein4 ≠ 0 :=
    intSeriesC_ne_zero_of_coeff K _ 0 (by simp [ModularCurve.eisenstein4])
  have hdt : ModularCurve.intSeriesC K pDel * ModularCurve.qEuler K (ModularCurve.jqModC K) =
      -(ModularCurve.intSeriesC K ModularCurve.eisenstein4 * ModularCurve.intSeriesC K ModularCurve.eisenstein4 *
        ModularCurve.intSeriesC K ModularCurve.eisenstein6) := by
    apply mul_left_cancel₀ he4
    linear_combination (ModularCurve.intSeriesC K pDel) * hR - (ModularCurve.intSeriesC K ModularCurve.eisenstein6) * hjD
  have hden : ModularCurve.intSeriesC K (pE14w pEw) =
      ModularCurve.intSeriesC K ModularCurve.eisenstein4 * ModularCurve.intSeriesC K ModularCurve.eisenstein4 *
        ModularCurve.intSeriesC K ModularCurve.eisenstein6 * HahnSeries.C (s : K) := by
    rw [pE14w, ModularCurve.intSeriesC_mul, ModularCurve.intSeriesC_mul, ModularCurve.intSeriesC_mul, hpEw]
  have hnum : ModularCurve.intSeriesC K (P * pDel + pE14w pEw) =
      HahnSeries.C ((D₁ : ℕ) : K) * ModularCurve.intSeriesC K pf * ModularCurve.intSeriesC K pDel +
        ModularCurve.intSeriesC K ModularCurve.eisenstein4 * ModularCurve.intSeriesC K ModularCurve.eisenstein4 *
          ModularCurve.intSeriesC K ModularCurve.eisenstein6 * HahnSeries.C (s : K) := by
    rw [← hden, ← hPred, ← ModularCurve.intSeriesC_mul]
    unfold ModularCurve.intSeriesC
    rw [map_add, map_add]
  have he6 : ModularCurve.intSeriesC K ModularCurve.eisenstein6 ≠ 0 :=
    intSeriesC_ne_zero_of_coeff K _ 0 (by simp [ModularCurve.eisenstein6])
  have hE0 : ModularCurve.intSeriesC K ModularCurve.eisenstein4 * ModularCurve.intSeriesC K ModularCurve.eisenstein4 *
        ModularCurve.intSeriesC K ModularCurve.eisenstein6 * HahnSeries.C (s : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero he4 he4) he6) (HahnSeries.C_ne_zero hsK)
  have hden0 : ModularCurve.intSeriesC K (pE14w pEw) ≠ 0 := hden ▸ hE0
  have h5' : ModularCurve.intSeriesC K (P * pDel + pE14w pEw) / ModularCurve.intSeriesC K (pE14w pEw) *
      ModularCurve.intSeriesC K (pE14w pEw) =
      HahnSeries.C ((D₁ : ℕ) : K) * ModularCurve.intSeriesC K pf * ModularCurve.intSeriesC K pDel +
        ModularCurve.intSeriesC K ModularCurve.eisenstein4 * ModularCurve.intSeriesC K ModularCurve.eisenstein4 *
          ModularCurve.intSeriesC K ModularCurve.eisenstein6 * HahnSeries.C (s : K) := by
    rw [div_mul_cancel₀ _ hden0, hnum]
  have h5 : ModularCurve.intSeriesC K (P * pDel + pE14w pEw) / ModularCurve.intSeriesC K (pE14w pEw) *
      (ModularCurve.intSeriesC K ModularCurve.eisenstein4 * ModularCurve.intSeriesC K ModularCurve.eisenstein4 *
        ModularCurve.intSeriesC K ModularCurve.eisenstein6 * HahnSeries.C (s : K)) =
      HahnSeries.C ((D₁ : ℕ) : K) * ModularCurve.intSeriesC K pf * ModularCurve.intSeriesC K pDel +
        ModularCurve.intSeriesC K ModularCurve.eisenstein4 * ModularCurve.intSeriesC K ModularCurve.eisenstein4 *
          ModularCurve.intSeriesC K ModularCurve.eisenstein6 * HahnSeries.C (s : K) := by
    calc _ = ModularCurve.intSeriesC K (P * pDel + pE14w pEw) / ModularCurve.intSeriesC K (pE14w pEw) *
          ModularCurve.intSeriesC K (pE14w pEw) := by rw [hden]
      _ = _ := h5'

  have hu : HahnSeries.C ((D₁ : ℕ) : K) * HahnSeries.C (((D₁ : ℕ) : K)⁻¹) = (1 : LaurentSeries K) := by
    rw [← map_mul, mul_inv_cancel₀ hD₁K, map_one]

  let Fbar := ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))
  let yelt : ↥Fbar := ⟨_, hy⟩
  let jelt : ↥Fbar := ⟨ModularCurve.jqModC K, hj⟩
  let c : K := -((s : K) * ((D₁ : ℕ) : K)⁻¹)
  let x₀ : ↥Fbar := algebraMap K (↥Fbar) c * (yelt - 1)
  have hcoe_c : ((algebraMap K (↥Fbar) c : ↥Fbar) : LaurentSeries K) =
      -(HahnSeries.C (s : K) * HahnSeries.C (((D₁ : ℕ) : K)⁻¹)) := by
    change algebraMap K (LaurentSeries K) c = _
    rw [ModularCurve.algebraMap_laurentSeries_apply_alt K c, ← HahnSeries.C_apply, ← map_mul, ← map_neg]
  have hcoe_x₀ : ((x₀ : ↥Fbar) : LaurentSeries K) =
      -(HahnSeries.C (s : K) * HahnSeries.C (((D₁ : ℕ) : K)⁻¹)) *
        (ModularCurve.intSeriesC K (P * pDel + pE14w pEw) / ModularCurve.intSeriesC K (pE14w pEw) - 1) := by
    show (((algebraMap K (↥Fbar) c * (yelt - 1)) : ↥Fbar) : LaurentSeries K) = _
    rw [IntermediateField.coe_mul, hcoe_c]
    congr 1
  have hx₀t : ((x₀ : ↥Fbar) : LaurentSeries K) * ModularCurve.qEuler K (ModularCurve.jqModC K) =
      ModularCurve.intSeriesC K pf := by
    rw [hcoe_x₀]
    exact x0_identity _ _ _ _ _ _ _ _ h5 hdt hu (hden ▸ hden0)

  have hΘω := hρinf f hf pf hpf
  have hinj := ModularCurve.diffQExp_qExpFunctionFieldC_injective K
    (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) (T_mem_GammaH _ _)
  have hω : ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
      ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) =
      x₀ • KaehlerDifferential.D K (↥Fbar) jelt := by
    apply hinj
    rw [hΘω, ModularCurve.diffQExp_smul_D]
    exact hx₀t.symm

  rw [hω, AlgebraicCurve.Differential.pullbackAlong_smul, AlgebraicCurve.Differential.pullbackAlong_D,
    AlgEquiv.toAlgHom_apply, AlgEquiv.toAlgHom_apply, ModularCurve.diffQExp_smul_D]

  have hσx₀ : ((σ x₀ : ↥Fbar) : LaurentSeries K) =
      -(HahnSeries.C (s : K) * HahnSeries.C (((D₁ : ℕ) : K)⁻¹)) * (((σ yelt : ↥Fbar) : LaurentSeries K) - 1) := by
    show (((σ (algebraMap K (↥Fbar) c * (yelt - 1))) : ↥Fbar) : LaurentSeries K) = _
    rw [map_mul, AlgEquiv.commutes, map_sub, map_one, IntermediateField.coe_mul, hcoe_c]
    congr 1

  have hσjelt : ((σ jelt : ↥Fbar) : LaurentSeries K) = ModularCurve.qExpand K (M / p) (ModularCurve.jqModC K) := hσj
  have hEq : ModularCurve.qEuler K (ModularCurve.qExpand K (M / p) (ModularCurve.jqModC K)) =
      HahnSeries.C ((M / p : ℕ) : K) * ModularCurve.qExpand K (M / p) (ModularCurve.qEuler K (ModularCurve.jqModC K)) := by
    have h := ModularCurve.thetaL_qExpand K (M / p) (ModularCurve.jqModC K)
    rw [thetaL_eq_qEuler, thetaL_eq_qEuler, ← HahnSeries.C_apply] at h
    exact h
  rw [← HahnSeries.C_mul_eq_smul, hσx₀, hσjelt, hEq]

  have hq : ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K pDel) *
      ModularCurve.qExpand K (M / p) (ModularCurve.qEuler K (ModularCurve.jqModC K)) =
      -(ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein4) *
        ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein4) *
        ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein6)) := by
    have h := congrArg (ModularCurve.qExpand K (M / p)) hdt
    rw [map_mul, map_neg, map_mul, map_mul] at h
    exact h
  have hqden : ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K (pE14w pEw)) =
      ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein4) *
        ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein4) *
        ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein6) * HahnSeries.C ((s : ℕ) : K) := by
    rw [hden, map_mul, map_mul, map_mul, ModularCurve.qExpand_C]
  rw [hqden, map_mul HahnSeries.C, map_mul HahnSeries.C, map_pow HahnSeries.C, map_pow HahnSeries.C] at hσy
  have h4 : HahnSeries.C ((D : ℕ) : K) * HahnSeries.ofPowerSeries ℤ K (PGW.map φ) =
      HahnSeries.C ((D₂ : ℕ) : K) * HahnSeries.C ((D₁ : ℕ) : K) * HahnSeries.C ((M / p : ℕ) : K) ^ w *
        HahnSeries.ofPowerSeries ℤ K (pfW.map φ) := by
    rw [hPGWred]
    push_cast
    rw [map_mul, map_mul, map_pow]
  have hqinj : Function.Injective (ModularCurve.qExpand K (M / p)) := ModularCurve.qExpand_injective (M / p)
  have hqe4 : ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein4) ≠ 0 :=
    (map_ne_zero_iff _ hqinj).mpr he4
  have hqe6 : ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein6) ≠ 0 :=
    (map_ne_zero_iff _ hqinj).mpr he6
  have hZ : HahnSeries.C ((D₂ : ℕ) : K) * HahnSeries.C ((M / p : ℕ) : K) ^ (13 + w) *
      (ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein4) *
        ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein4) *
        ModularCurve.qExpand K (M / p) (ModularCurve.intSeriesC K ModularCurve.eisenstein6) * HahnSeries.C ((s : ℕ) : K)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (HahnSeries.C_ne_zero hD₂K) (pow_ne_zero _ (HahnSeries.C_ne_zero hQK)))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hqe4 hqe4) hqe6) (HahnSeries.C_ne_zero hsK))
  exact final_identity _ _ _ _ _ _ _ _ _ _ _ _ w hσy h4 hq hu hZ

end
end S_ModularCurve_IsInfReductionMap_smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke
end P2MW
export P2MW.S_ModularCurve_IsInfReductionMap_smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke (solution)
