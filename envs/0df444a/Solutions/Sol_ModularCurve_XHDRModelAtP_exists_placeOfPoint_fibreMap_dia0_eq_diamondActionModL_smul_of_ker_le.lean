-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fbe8c56c-d6fd-58e5-a6ac-14de18f0d250

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_algEquiv_chartAlgFin_gammaH_infSubgroup_forall_coeffEmb_eq_diamondAutHBar_symm
import Theorems.Thm_ModularCurve_XHDRModelAtP_iotaFin_comp_dia0_hom_eq_spec_map_comp_iotaFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC ModularForm UpperHalfPlane CongruenceSubgroup"
open scoped MatrixGroups ModularForm Pointwise

namespace DiaRedU

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

abbrev ΓH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ΓH M H ≤ ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • ΓH M H := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨γ * δ * γ⁻¹, CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨δ, hδ⟩, by simp; rfl⟩

def slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓH M H) k) :
    ModularForm (ΓH M H) k :=
  restrictForm (le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓH M H) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] γ := rfl

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (ΓH M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

theorem exists_integral_pair {k : ℤ} (a : ModularForm (ΓH M H) k) {pa : PowerSeries ℤ}
    (ha : IsIntegralQExp a pa) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ∃ (c : ℕ) (F F₁ : ModularForm (ΓH M H) k) (pF : PowerSeries ℤ),
      IsIntegralQExp F pF ∧ IsIntegralQExp F₁ ((PowerSeries.C ((M : ℤ) ^ c)) * pa) ∧
      (⇑F : ℍ → ℂ) = ((M : ℂ) ^ c) • ((⇑a : ℍ → ℂ) ∣[k] γ⁻¹) ∧
      (⇑F₁ : ℍ → ℂ) = ((⇑F : ℍ → ℂ) ∣[k] γ) := by
  have hle : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ ΓH M H :=
    Subgroup.map_mono (Gamma1_le_GammaH M H)
  obtain ⟨c, f₁, p₁, hf₁, hf₁s⟩ :=
    ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 M (restrictForm hle a)
      (by rw [IsIntegralQExp, coe_restrictForm]; exact ha) γ⁻¹ (inv_mem hγ)
  have hF : (⇑(((M : ℂ) ^ c) • slashForm γ⁻¹ (inv_mem hγ) a) : ℍ → ℂ) = ((M : ℂ) ^ c) • ((⇑a : ℍ → ℂ) ∣[k] γ⁻¹) := by
    rw [ModularForm.IsGLPos.coe_smul, coe_slashForm]
  have hF₁ : (⇑(((M : ℂ) ^ c) • a) : ℍ → ℂ) = ((M : ℂ) ^ c) • (⇑a : ℍ → ℂ) := ModularForm.IsGLPos.coe_smul _ _
  refine ⟨c, ((M : ℂ) ^ c) • slashForm γ⁻¹ (inv_mem hγ) a, ((M : ℂ) ^ c) • a, p₁, ?_, ?_, hF, ?_⟩
  ·
    have : (⇑(((M : ℂ) ^ c) • slashForm γ⁻¹ (inv_mem hγ) a) : ℍ → ℂ) = ⇑f₁ := by
      rw [hF, hf₁s, coe_restrictForm]
    rw [IsIntegralQExp, this]
    exact hf₁
  · rw [IsIntegralQExp, map_mul, PowerSeries.map_C, ha, hF₁, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods,
      PowerSeries.smul_eq_C_mul, eq_intCast, Int.cast_pow, Int.cast_natCast]
  · rw [hF₁, hF, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

theorem intSeriesC_ne_zero_of_pair (K : Type*) [Field K] (hM : (M : K) ≠ 0) {k : ℤ}
    (b : ModularForm (ΓH M H) k) {pb : PowerSeries ℤ} (hb : IsIntegralQExp b pb) (hb0 : intSeriesC K pb ≠ 0)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {c : ℕ} (G : ModularForm (ΓH M H) k) {pG : PowerSeries ℤ}
    (hG : IsIntegralQExp G pG) (hGs : (⇑G : ℍ → ℂ) = ((M : ℂ) ^ c) • ((⇑b : ℍ → ℂ) ∣[k] γ⁻¹)) :
    intSeriesC K pG ≠ 0 := by
  intro h0

  have hcoef : ∀ n : ℕ, ((PowerSeries.coeff n pG : ℤ) : K) = 0 := by
    intro n
    have := congrArg (fun z : LaurentSeries K => z.coeff n) h0
    simp only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast,
      HahnSeries.coeff_zero] at this
    exact this
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K

  have hdvd : ∀ n : ℕ, (ℓ : ℤ) ∣ PowerSeries.coeff n pG := fun n =>
    (CharP.intCast_eq_zero_iff K ℓ _).mp (hcoef n)
  let q : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff n pG / ℓ
  have hq : pG = PowerSeries.C (ℓ : ℤ) * q := by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    exact (Int.mul_ediv_cancel' (hdvd n)).symm
  rcases CharP.char_is_prime_or_zero K ℓ with hprime | hzero
  ·
    have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hprime.ne_zero
    let G' : ModularForm (ΓH M H) k := ((ℓ : ℂ)⁻¹) • G
    have hG' : IsIntegralQExp (⇑G') q := by
      rw [IsIntegralQExp, show (⇑G' : ℍ → ℂ) = ((ℓ : ℂ)⁻¹) • (⇑G : ℍ → ℂ) from ModularForm.IsGLPos.coe_smul _ _,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods, ← hG, hq, map_mul, PowerSeries.map_C,
        eq_intCast, Int.cast_natCast, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hℓ0,
        map_one, one_mul]
    obtain ⟨c', F, F₁, pF, hF, -, hFs, -⟩ := exists_integral_pair G' hG' γ⁻¹ (inv_mem hγ)
    rw [inv_inv] at hFs

    have hfun : (ℓ : ℂ) • (⇑F : ℍ → ℂ) = ((M : ℂ) ^ (c + c')) • (⇑b : ℍ → ℂ) := by
      rw [hFs, show (⇑G' : ℍ → ℂ) = ((ℓ : ℂ)⁻¹) • (⇑G : ℍ → ℂ) from ModularForm.IsGLPos.coe_smul _ _, hGs,
        ModularForm.SL_smul_slash, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, inv_mul_cancel,
        SlashAction.slash_one, smul_smul, smul_smul, smul_smul, pow_add]
      congr 1
      field_simp

    have h1 : IsIntegralQExp ((ℓ : ℂ) • (⇑F : ℍ → ℂ)) (PowerSeries.C (ℓ : ℤ) * pF) := by
      rw [IsIntegralQExp, map_mul, PowerSeries.map_C, eq_intCast, Int.cast_natCast, hF,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods, PowerSeries.smul_eq_C_mul]
    have h2 : IsIntegralQExp (((M : ℂ) ^ (c + c')) • (⇑b : ℍ → ℂ)) (PowerSeries.C ((M : ℤ) ^ (c + c')) * pb) := by
      rw [IsIntegralQExp, map_mul, PowerSeries.map_C, eq_intCast, Int.cast_pow, Int.cast_natCast, hb,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods, PowerSeries.smul_eq_C_mul]
    rw [hfun] at h1
    have heq : PowerSeries.C (ℓ : ℤ) * pF = PowerSeries.C ((M : ℤ) ^ (c + c')) * pb := h1.unique h2

    have : intSeriesC K (PowerSeries.C ((M : ℤ) ^ (c + c')) * pb) = 0 := by
      rw [← heq, intSeriesC_mul]
      have : intSeriesC K (PowerSeries.C (ℓ : ℤ)) = 0 := by
        rw [intSeriesC, PowerSeries.map_C, eq_intCast, Int.cast_natCast, CharP.cast_eq_zero, map_zero, map_zero]
      rw [this, zero_mul]
    rw [intSeriesC_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · apply hM
      rw [intSeriesC, PowerSeries.map_C, eq_intCast, Int.cast_pow, Int.cast_natCast, HahnSeries.ofPowerSeries_C] at h
      by_contra hM'
      exact HahnSeries.C_ne_zero (pow_ne_zero _ hM') h
    · exact hb0 h
  ·
    subst hzero
    have hpG : pG = 0 := by
      ext n
      rw [map_zero]
      exact zero_dvd_iff.mp (hdvd n)
    have hG0 : (⇑G : ℍ → ℂ) = 0 := by
      have : UpperHalfPlane.qExpansion 1 ⇑G = 0 := by rw [← hG, hpG, map_zero]
      have hG00 : G = 0 := (ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods G).mp this
      rw [hG00]; rfl
    have hb00 : (⇑b : ℍ → ℂ) = 0 := by
      have hMc : ((M : ℂ) ^ c) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (NeZero.ne M))
      have h1 : ((⇑b : ℍ → ℂ) ∣[k] γ⁻¹) = 0 := by
        have := hGs.symm.trans hG0
        exact (smul_eq_zero.mp this).resolve_left hMc
      have h2 : (⇑b : ℍ → ℂ) = (((⇑b : ℍ → ℂ) ∣[k] γ⁻¹) ∣[k] γ) := by
        rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
      rw [h2, h1, SlashAction.zero_slash]
    apply hb0
    have : pb = 0 := by
      have hq0 : UpperHalfPlane.qExpansion 1 (⇑b : ℍ → ℂ) = 0 := by
        rw [hb00]; exact UpperHalfPlane.qExpansion_zero 1
      apply (PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective)
      rw [hb, hq0, map_zero]
    rw [this, intSeriesC_zero]

theorem exists_integral_pair₂ {k : ℤ} (a b : ModularForm (ΓH M H) k) {pa pb : PowerSeries ℤ}
    (ha : IsIntegralQExp a pa) (hb : IsIntegralQExp b pb) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ∃ (c : ℕ) (F G F₁ G₁ : ModularForm (ΓH M H) k) (pF pG : PowerSeries ℤ),
      IsIntegralQExp F pF ∧ IsIntegralQExp G pG ∧
      IsIntegralQExp F₁ ((PowerSeries.C ((M : ℤ) ^ c)) * pa) ∧ IsIntegralQExp G₁ ((PowerSeries.C ((M : ℤ) ^ c)) * pb) ∧
      (⇑F : ℍ → ℂ) = ((M : ℂ) ^ c) • ((⇑a : ℍ → ℂ) ∣[k] γ⁻¹) ∧
      (⇑G : ℍ → ℂ) = ((M : ℂ) ^ c) • ((⇑b : ℍ → ℂ) ∣[k] γ⁻¹) ∧
      (⇑F₁ : ℍ → ℂ) = ((⇑F : ℍ → ℂ) ∣[k] γ) ∧ (⇑G₁ : ℍ → ℂ) = ((⇑G : ℍ → ℂ) ∣[k] γ) := by
  obtain ⟨c₁, F, F₁, pF, hF, hF₁, hFs, hF₁s⟩ := exists_integral_pair a ha γ hγ
  obtain ⟨c₂, G, G₁, pG, hG, hG₁, hGs, hG₁s⟩ := exists_integral_pair b hb γ hγ
  have sF : ∀ (e : ℕ) (X : ModularForm (ΓH M H) k), (⇑(((M : ℂ) ^ e) • X) : ℍ → ℂ) = ((M : ℂ) ^ e) • (⇑X : ℍ → ℂ) :=
    fun e X => ModularForm.IsGLPos.coe_smul _ _
  have iF : ∀ (e : ℕ) (X : ModularForm (ΓH M H) k) (q : PowerSeries ℤ), IsIntegralQExp X q →
      IsIntegralQExp (⇑(((M : ℂ) ^ e) • X)) (PowerSeries.C ((M : ℤ) ^ e) * q) := by
    intro e X q hX
    rw [IsIntegralQExp, map_mul, PowerSeries.map_C, eq_intCast, Int.cast_pow, Int.cast_natCast, hX, sF,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods, PowerSeries.smul_eq_C_mul]
  refine ⟨c₁ + c₂, ((M : ℂ) ^ c₂) • F, ((M : ℂ) ^ c₁) • G, ((M : ℂ) ^ c₂) • F₁, ((M : ℂ) ^ c₁) • G₁,
    PowerSeries.C ((M : ℤ) ^ c₂) * pF, PowerSeries.C ((M : ℤ) ^ c₁) * pG, iF _ _ _ hF, iF _ _ _ hG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := iF c₂ F₁ _ hF₁
    rwa [← mul_assoc, ← map_mul, ← pow_add, add_comm] at this
  · have := iF c₁ G₁ _ hG₁
    rwa [← mul_assoc, ← map_mul, ← pow_add] at this
  · rw [sF, hFs, smul_smul, ← pow_add, add_comm]
  · rw [sF, hGs, smul_smul, ← pow_add]
  · rw [sF, sF, hF₁s, ModularForm.SL_smul_slash]
  · rw [sF, sF, hG₁s, ModularForm.SL_smul_slash]

theorem intSeriesC_sub (K : Type*) [Field K] (q q' : PowerSeries ℤ) :
    intSeriesC K (q - q') = intSeriesC K q - intSeriesC K q' := by
  simp [intSeriesC]

theorem intSeriesC_C (K : Type*) [Field K] (z : ℤ) : intSeriesC K (PowerSeries.C z) = HahnSeries.C (z : K) := by
  rw [intSeriesC, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C]

end DiaRedU
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le.DiaRedU"

namespace DiaRedQ

p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC"

section ContentNorm

variable (p : ℕ) [hp : Fact p.Prime]

theorem pow_dvd_of_eq_pow_mul (m : ℕ) (a : ℤ) (z : ℚ) (hz : z ∈ GaloisRep.ratLocalizedAt p)
    (h : (a : ℚ) = (p : ℚ) ^ m * z) : (p : ℤ) ^ m ∣ a := by
  have hden : z.den.Coprime p := hz
  have h1 : (a : ℚ) * z.den = (p : ℚ) ^ m * z.num := by
    rw [h, mul_assoc, Rat.mul_den_eq_num]
  have h2 : a * (z.den : ℤ) = (p : ℤ) ^ m * z.num := by exact_mod_cast h1
  have hcop : IsCoprime ((p : ℤ) ^ m) (z.den : ℤ) := by
    have := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left m hden.symm)
    simpa [Nat.cast_pow] using this
  exact hcop.dvd_of_dvd_mul_right ⟨z.num, h2⟩

theorem coeffMap_ofPowerSeries_map {R S : Type*} [CommRing R] [CommRing S] (τ : R →+* S) (P : PowerSeries ℤ) :
    coeffMap τ (HahnSeries.ofPowerSeries ℤ R (P.map (Int.castRingHom R))) =
      HahnSeries.ofPowerSeries ℤ S (P.map (Int.castRingHom S)) := by
  ext i
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero τ
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]

theorem coeffMap_intSeriesC {K K' : Type*} [Field K] [Field K'] (τ : K →+* K') (P : PowerSeries ℤ) :
    coeffMap τ (intSeriesC K P) = intSeriesC K' P :=
  coeffMap_ofPowerSeries_map τ P

theorem intSeriesC_eq_zero_of {K : Type*} [Field K] {P : PowerSeries ℤ} (h : intSeriesC ℚ P = 0) :
    intSeriesC K P = 0 := by
  have hP : P = 0 := by
    apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
    have : HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ)) = HahnSeries.ofPowerSeries ℤ ℚ 0 := by
      rw [map_zero]; exact h
    rw [map_zero]
    exact HahnSeries.ofPowerSeries_injective this
  rw [hP, intSeriesC_zero]

theorem exists_ratio_intSeriesC_ne_zero (Γ : Subgroup SL(2, ℤ))
    (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)
    (K : Type*) [Field K] [CharP K p]
    (x : LaurentSeries ℚ) (hx : x ∈ qExpFunctionFieldC ℚ Γ)
    (y : LaurentSeries ↥(GaloisRep.ratLocalizedAt p))
    (hy : coeffMap (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) y = x) :
    ∃ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
      IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC K pg ≠ 0 ∧ intSeriesC ℚ pg ≠ 0 ∧
        x = intSeriesC ℚ pf / intSeriesC ℚ pg := by
  obtain ⟨k, f₀, g₀, pf₀, pg₀, hf₀, hg₀, hg0, hxfg⟩ :=
    (ModularCurve.mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC Γ hΓ x).mp hx

  let Pd : ℕ → Prop := fun m => ∀ n, (p : ℤ) ^ m ∣ PowerSeries.coeff n pg₀
  have hP0 : Pd 0 := fun n => by simp
  have hne : ∃ n, PowerSeries.coeff n pg₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hg0
    have : pg₀ = 0 := by ext n; simp [hall n]
    rw [this, intSeriesC_zero]
  have hPne : ∃ N, ¬ Pd N := by
    obtain ⟨n, hn⟩ := hne
    refine ⟨(PowerSeries.coeff n pg₀).natAbs, fun h => ?_⟩
    have hd := Int.natAbs_dvd_natAbs.mpr (h n)
    rw [Int.natAbs_pow, Int.natAbs_natCast] at hd
    have hlt : (PowerSeries.coeff n pg₀).natAbs < p ^ (PowerSeries.coeff n pg₀).natAbs :=
      Nat.lt_pow_self hp.out.one_lt
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hd) (not_le.mpr hlt)
  classical
  let N := Nat.find hPne
  have hN : ¬ Pd N := Nat.find_spec hPne
  have hN0 : N ≠ 0 := fun h => hN (h ▸ hP0)
  obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := Nat.exists_eq_succ_of_ne_zero hN0
  have hPm : Pd m := by
    have := Nat.find_min hPne (show m < N by omega)
    simpa using this

  let pg : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff n pg₀ / (p : ℤ) ^ m
  have hpg : pg₀ = PowerSeries.C ((p : ℤ) ^ m) * pg := by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    exact (Int.mul_ediv_cancel' (hPm n)).symm
  have hpgK : intSeriesC K pg ≠ 0 := by
    intro h0
    apply hN
    rw [hm]
    intro n
    have hc : ((PowerSeries.coeff n pg : ℤ) : K) = 0 := by
      have := congrArg (fun z : LaurentSeries K => z.coeff n) h0
      simpa only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast,
        HahnSeries.coeff_zero] using this
    obtain ⟨c, hc'⟩ := (CharP.intCast_eq_zero_iff K p _).mp hc
    refine ⟨c, ?_⟩
    rw [hpg, PowerSeries.coeff_C_mul, hc', pow_succ, mul_assoc]

  let W : LaurentSeries ↥(GaloisRep.ratLocalizedAt p) :=
    HahnSeries.ofPowerSeries ℤ _ (pg.map (Int.castRingHom _))
  have hmul : intSeriesC ℚ pf₀ = x * intSeriesC ℚ pg₀ := by
    rw [hxfg, div_mul_cancel₀ _ hg0]
  have hPf : ∀ n, (p : ℤ) ^ m ∣ PowerSeries.coeff n pf₀ := by
    intro n
    have hW : intSeriesC ℚ pg₀ = (p : ℚ) ^ m • coeffMap (algebraMap _ ℚ) W := by
      rw [hpg, intSeriesC_mul, show intSeriesC ℚ pg = coeffMap (algebraMap _ ℚ) W from
        (coeffMap_ofPowerSeries_map _ pg).symm, intSeriesC, PowerSeries.map_C, eq_intCast,
        HahnSeries.ofPowerSeries_C, Int.cast_pow, Int.cast_natCast, HahnSeries.C_mul_eq_smul]
    have key : intSeriesC ℚ pf₀ = (p : ℚ) ^ m • coeffMap (algebraMap _ ℚ) (y * W) := by
      rw [hmul, hW, ← hy, map_mul, mul_smul_comm]
    have hcoef := congrArg (fun z : LaurentSeries ℚ => z.coeff (n : ℤ)) key
    simp only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast,
      HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul] at hcoef
    exact pow_dvd_of_eq_pow_mul p m _ _ ((y * W).coeff n).2 hcoef
  let pf : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff n pf₀ / (p : ℤ) ^ m
  have hpf : pf₀ = PowerSeries.C ((p : ℤ) ^ m) * pf := by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    exact (Int.mul_ediv_cancel' (hPf n)).symm

  have hpC : ((p : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have scale : ∀ (F : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (P Q : PowerSeries ℤ),
      IsIntegralQExp F P → P = PowerSeries.C ((p : ℤ) ^ m) * Q → IsIntegralQExp (⇑(((p : ℂ) ^ m)⁻¹ • F)) Q := by
    intro F P Q hF hPQ
    rw [IsIntegralQExp, show (⇑(((p : ℂ) ^ m)⁻¹ • F) : ℍ → ℂ) = ((p : ℂ) ^ m)⁻¹ • (⇑F : ℍ → ℂ) from
        ModularForm.IsGLPos.coe_smul _ _, ModularForm.qExpansion_smul one_pos hΓ, ← hF, hPQ, map_mul,
      PowerSeries.map_C, eq_intCast, Int.cast_pow, Int.cast_natCast, PowerSeries.smul_eq_C_mul, ← mul_assoc,
      ← map_mul, inv_mul_cancel₀ hpC, map_one, one_mul]
  refine ⟨k, ((p : ℂ) ^ m)⁻¹ • f₀, ((p : ℂ) ^ m)⁻¹ • g₀, pf, pg, scale f₀ pf₀ pf hf₀ hpf, scale g₀ pg₀ pg hg₀ hpg,
    hpgK, fun h => hpgK (intSeriesC_eq_zero_of h), ?_⟩
  have hC : intSeriesC ℚ (PowerSeries.C ((p : ℤ) ^ m)) ≠ 0 := by
    rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
    rw [eq_intCast]
    exact HahnSeries.C_ne_zero (by push_cast; exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero))
  rw [hxfg, hpf, hpg, intSeriesC_mul, intSeriesC_mul, mul_div_mul_left _ _ hC]

end ContentNorm
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le.DiaRedU"

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  exact hf (by simpa only [coeffMap_coeff] using congrArg (fun z : LaurentSeries S => z.coeff k) h)

theorem coeffMap_eq_div (p : ℕ) {y : LaurentSeries ↥(GaloisRep.ratLocalizedAt p)} {x : LaurentSeries ℚ}
    (hy : coeffMap (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) y = x)
    {P Q : PowerSeries ℤ} (hx : x * intSeriesC ℚ Q = intSeriesC ℚ P)
    {S : Type*} [Field S] (τ : ↥(GaloisRep.ratLocalizedAt p) →+* S) (hQS : intSeriesC S Q ≠ 0) :
    coeffMap τ y = intSeriesC S P / intSeriesC S Q := by
  have hR : y * HahnSeries.ofPowerSeries ℤ _ (Q.map (Int.castRingHom _)) =
      HahnSeries.ofPowerSeries ℤ _ (P.map (Int.castRingHom _)) := by
    apply coeffMap_injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) Subtype.val_injective
    rw [map_mul, coeffMap_ofPowerSeries_map, coeffMap_ofPowerSeries_map, hy]
    exact hx
  have := congrArg (coeffMap τ) hR
  rw [map_mul, coeffMap_ofPowerSeries_map, coeffMap_ofPowerSeries_map] at this
  rw [eq_div_iff hQS]
  exact this

end DiaRedQ
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le.DiaRedU"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective~coeffMap_intSeriesC ModularCurve.XHDRLevel"

open scoped MatrixGroups

namespace DiaRed

variable {p : ℕ} [Fact p.Prime]
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

section Generic

variable {Γ : Subgroup SL(2, ℤ)}
variable {κ : Type} [Field κ] [IsAlgClosed κ] [Algebra (R p) κ]
variable {L : Type} [Field L] [Algebra κ L]
variable (Mf : CurveModel κ L)
  (ef : Mf.C ⟶ pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))))

def readFin
    [Nonempty (Scheme.Opens.toScheme
      ((ef ≫ pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) ⁻¹ᵁ ((ιFin p Γ hj) ''ᵁ ⊤)))]
    (b : ↥(chartAlgFin p Γ hj)) : L :=
  Mf.ffEquiv.symm
    (Mf.C.germToFunctionField
      ((ef ≫ pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) ⁻¹ᵁ ((ιFin p Γ hj) ''ᵁ ⊤))
      (((ef ≫ pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))).app ((ιFin p Γ hj) ''ᵁ ⊤)).hom
        (((ιFin p Γ hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p Γ hj))).inv b))))

theorem finiteAlong_algEquiv (Φ : L ≃ₐ[κ] L) : FiniteAlong κ Φ.toAlgHom :=
  RingHom.Finite.of_surjective Φ.toAlgHom.toRingHom Φ.surjective

theorem isIntegral_algEquiv (Φ : L ≃ₐ[κ] L) : Φ.toAlgHom.toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective Φ.toAlgHom.toRingHom Φ.surjective

theorem placeOfPoint_fibreMap_eq_smul
    [hne : Nonempty (Scheme.Opens.toScheme
      ((ef ≫ pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) ⁻¹ᵁ ((ιFin p Γ hj) ''ᵁ ⊤)))]
    [IsIso ef] (hef : ef ≫ pullback.snd _ _ = Mf.toBase)
    (w : X p Γ hj ≅ X p Γ hj) (hw : w.hom ≫ toBase p Γ hj = toBase p Γ hj)
    (σ : ↥(chartAlgFin p Γ hj) ≃ₐ[R p] ↥(chartAlgFin p Γ hj))
    (hchart : ιFin p Γ hj ≫ w.hom = Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ ιFin p Γ hj)
    (Φ : L ≃ₐ[κ] L) (hΦ : ∀ b, Φ (readFin Mf ef b) = readFin Mf ef (σ b))
    (P : closedPoints Mf.C) :
    ∃ h : (inv ef).base ((fibreMap (overOfIso w hw) (algebraMap (R p) κ)).base (ef.base P.1)) ∈ closedPoints Mf.C,
      Mf.placeOfPoint ⟨_, h⟩ = SemilinearAut.ofAlgAut Φ.symm • Mf.placeOfPoint P := by

  have hinv : inv ef ≫ Mf.toBase = pullback.snd _ _ := by
    rw [IsIso.inv_comp_eq, hef]
  let θ : Mf.C ⟶ Mf.C := ef ≫ fibreMap (overOfIso w hw) (algebraMap (R p) κ) ≫ inv ef
  have hθ : θ ≫ Mf.toBase = Mf.toBase := by
    simp only [θ, Category.assoc, hinv, fibreMap, pullback.lift_snd, Category.comp_id]
    exact hef
  let x₀ : {q : Spec (CommRingCat.of κ) ⟶ Mf.C // q ≫ Mf.toBase = 𝟙 _} := (pointEquivClosedPoint Mf.toBase).symm P
  let x₁ : {q : Spec (CommRingCat.of κ) ⟶ Mf.C // q ≫ Mf.toBase = 𝟙 _} :=
    ⟨x₀.1 ≫ θ, by rw [Category.assoc, hθ, x₀.2]⟩
  have hyx : x₁.1 ≫ ef ≫ pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))) =
      x₀.1 ≫ ef ≫ pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))) ≫ w.hom := by
    show (x₀.1 ≫ θ) ≫ _ = _
    simp only [θ, Category.assoc, IsIso.inv_hom_id_assoc, fibreMap, pullback.lift_fst]
    rfl
  have hchart' : ιFin p Γ hj ≫ w.hom = Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ ιFin p Γ hj := hchart
  have key := AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin (R p) κ
      ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
      (readFin Mf ef) (readFin Mf ef) Mf ef hef hne (fun _ => rfl) Mf ef hef hne (fun _ => rfl)
      w.hom hw σ.toAlgHom hchart' Φ.toAlgHom hΦ (isIntegral_algEquiv Φ) (finiteAlong_algEquiv Φ) x₀ x₁ hyx
  rw [AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul] at key

  have h0 : Mf.pointEquivPlace x₀ = Mf.placeOfPoint P := by
    rw [CurveModel.pointEquivPlace_apply]; congr 1; exact Equiv.apply_symm_apply _ P
  have hpt : x₁.1.base (closedPoint κ) =
      (inv ef).base ((fibreMap (overOfIso w hw) (algebraMap (R p) κ)).base (ef.base P.1)) := by
    show (x₀.1 ≫ θ).base (closedPoint κ) = _
    have : x₀.1.base (closedPoint κ) = P.1 :=
      congrArg Subtype.val ((pointEquivClosedPoint Mf.toBase).apply_symm_apply P)
    simp only [θ, Scheme.Hom.comp_apply, this]
  have hmem : (inv ef).base ((fibreMap (overOfIso w hw) (algebraMap (R p) κ)).base (ef.base P.1)) ∈ closedPoints Mf.C := by
    rw [← hpt]; exact (pointEquivClosedPoint Mf.toBase x₁).2
  refine ⟨hmem, ?_⟩
  have h1 : Mf.pointEquivPlace x₁ = Mf.placeOfPoint ⟨_, hmem⟩ := by
    rw [CurveModel.pointEquivPlace_apply]; congr 1; exact Subtype.ext hpt
  rw [← h1, key, h0]

end Generic
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le.DiaRedU"

section DiaRead

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
variable {κ : Type} [Field κ] [IsAlgClosed κ] [CharP κ p] [Algebra (R p) κ]
variable (Mf : CurveModel κ ↥(qExpFunctionFieldC κ (ΓN p M H hpM)))
  (ef : Mf.C ⟶ pullback (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ))))

theorem diamondActionModL_readFin_sigma
    [Nonempty (Scheme.Opens.toScheme
      ((ef ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) ⁻¹ᵁ
        ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
    (hpM2 : ¬ p ^ 2 ∣ M)
    (pinR : ∀ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) →
      ((readFin Mf ef b : ↥(qExpFunctionFieldC κ (ΓN p M H hpM))) : LaurentSeries κ) = coeffMap (algebraMap (R p) κ) y)
    (e : (ZMod (M / p))ˣ)
    (σ : ↥(chartAlgFin p (ΓN p M H hpM) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (hσ : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      coeffEmb (AlgebraicClosure ℚ) (((σ b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) =
        (((diamondAutHBar (M / p) (infSubgroup p M H hpM) e).symm
            ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))).2⟩
          : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)))
    (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) :
    diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e) (readFin Mf ef (σ b)) =
      readFin Mf ef b := by
  have hp : p.Prime := Fact.out

  have hpN : ¬ p ∣ M / p := by
    rintro ⟨t, ht⟩
    exact hpM2 ⟨t, by rw [← Nat.mul_div_cancel' hpM, ht, pow_two, mul_assoc]⟩
  have hNκ : ((M / p : ℕ) : κ) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff κ p _).mp h)

  have hlaw : IsDiamondPullbackModL κ (M / p) (infSubgroup p M H hpM)
      (diamondActionModL κ (M / p) (infSubgroup p M H hpM)) :=
    isDiamondPullbackModL_diamondActionModL
      (ModularCurve.exists_isDiamondPullbackModL_of_isAlgClosed κ (M / p) hNκ _)

  obtain ⟨yb, hyb⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓN p M H hpM) p (jAt (ΓN p M H hpM) hj) (coe_jAt _ _)).1 b
  obtain ⟨yc, hyc⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓN p M H hpM) p (jAt (ΓN p M H hpM) hj) (coe_jAt _ _)).1 (σ b)

  obtain ⟨k, f, g, pf, pg, hf, hg, hgκ, hgℚ, hcfg⟩ :=
    DiaRedQ.exists_ratio_intSeriesC_ne_zero p (ΓN p M H hpM)
      (DiaRedU.one_mem_strictPeriods (M := M / p) (H := infSubgroup p M H hpM)) κ _
      ((σ b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))).2 yc hyc

  set γ₀ : Gamma0 (M / p) := CuspForm.gammaLift (M / p) e with hγ₀
  have h00 : ((((γ₀⁻¹ : Gamma0 (M / p)) : SL(2, ℤ)) 0 0 : ℤ) : ZMod (M / p)) = (e : ZMod (M / p)) := by
    have h1 : (((γ₀⁻¹ : Gamma0 (M / p)) : SL(2, ℤ)) 0 0 : ℤ) = ((γ₀ : SL(2, ℤ)) 1 1 : ℤ) := by
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rw [h1]
    have := CuspForm.gamma0Units_gammaLift (M := M / p) e
    rw [← this, CohCarrier.val_gamma0Units]
    rfl

  have hDA := (ModularCurve.heckeDiamondInputsHAll (M / p) (infSubgroup p M H hpM)).isDiamondAutHBar e
  obtain ⟨y, hyF, hσy, hymul⟩ := hDA k f g pf pg hf hg hgℚ _ (γ₀⁻¹).2 h00
  have hb_y : ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) = y := by
    apply DiaRedQ.coeffMap_injective (algebraMap ℚ (AlgebraicClosure ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    change coeffEmb (AlgebraicClosure ℚ) _ = coeffEmb (AlgebraicClosure ℚ) y
    rw [← hσy]
    have h1 := hσ b
    have h2 : (⟨coeffEmb (AlgebraicClosure ℚ)
          (((σ b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            ((σ b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))).2⟩ :
          ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
        (diamondAutHBar (M / p) (infSubgroup p M H hpM) e).symm
          ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))).2⟩ :=
      Subtype.ext h1
    have h3 := congrArg (diamondAutHBar (M / p) (infSubgroup p M H hpM) e) h2
    rw [AlgEquiv.apply_symm_apply] at h3
    refine (congrArg Subtype.val h3).symm.trans ?_
    congr 2
    exact Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) hcfg)

  obtain ⟨cN, F, G, F₁, G₁, pF, pG, hF, hG, hF₁, hG₁, hFs, hGs, hF₁s, hG₁s⟩ :=
    DiaRedU.exists_integral_pair₂ (M := M / p) (H := infSubgroup p M H hpM) f g hf hg (γ₀ : SL(2, ℤ)) γ₀.2
  have hG0 : intSeriesC κ pG ≠ 0 :=
    DiaRedU.intSeriesC_ne_zero_of_pair (M := M / p) (H := infSubgroup p M H hpM) κ hNκ g hg hgκ
      (γ₀ : SL(2, ℤ)) γ₀.2 G hG hGs
  have hG0ℚ : intSeriesC ℚ pG ≠ 0 := fun h => hG0 (DiaRedQ.intSeriesC_eq_zero_of h)

  have qexp_eq : ∀ (X : ModularForm (DiaRedU.ΓH (M / p) (infSubgroup p M H hpM)) k)
      (x : ModularForm (DiaRedU.ΓH (M / p) (infSubgroup p M H hpM)) k) (P : PowerSeries ℤ),
      IsIntegralQExp X P → (⇑X : ℍ → ℂ) = (((M / p : ℕ) : ℂ) ^ cN) • ((⇑x : ℍ → ℂ) ∣[k] (γ₀ : SL(2, ℤ))⁻¹) →
      intSeriesC ℂ P = HahnSeries.C ((((M / p : ℕ) : ℂ) ^ cN)) *
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ((⇑x : ℍ → ℂ) ∣[k] ((γ₀⁻¹ : Gamma0 (M / p)) : SL(2, ℤ)))) := by
    intro X x P hX hXs
    rw [intSeriesC, hX, hXs, show ((γ₀ : SL(2, ℤ))⁻¹) = ((γ₀⁻¹ : Gamma0 (M / p)) : SL(2, ℤ)) from rfl,
      ← DiaRedU.coe_slashForm _ (γ₀⁻¹).2, ModularForm.qExpansion_smul one_pos DiaRedU.one_mem_strictPeriods,
      PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C]
  have hbGF : ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) * intSeriesC ℚ pG = intSeriesC ℚ pF := by
    apply DiaRedQ.coeffMap_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    rw [map_mul, DiaRedQ.coeffMap_intSeriesC, DiaRedQ.coeffMap_intSeriesC, hb_y, qexp_eq G g pG hG hGs,
      qexp_eq F f pF hF hFs, mul_left_comm]
    congr 1

  have hcg : ((((σ b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) :
      LaurentSeries ℚ)) * intSeriesC ℚ pg = intSeriesC ℚ pf := by
    rw [hcfg, div_mul_cancel₀ _ hgℚ]
  have rb : ((readFin Mf ef b : ↥(qExpFunctionFieldC κ (ΓN p M H hpM))) : LaurentSeries κ) =
      intSeriesC κ pF / intSeriesC κ pG := by
    rw [pinR b yb hyb]
    exact DiaRedQ.coeffMap_eq_div p hyb hbGF _ hG0
  have hC : intSeriesC κ (PowerSeries.C (((M / p : ℕ) : ℤ) ^ cN)) ≠ 0 := by
    rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]
    rw [Int.cast_pow, Int.cast_natCast]
    exact HahnSeries.C_ne_zero (pow_ne_zero _ hNκ)
  have rc : ((readFin Mf ef (σ b) : ↥(qExpFunctionFieldC κ (ΓN p M H hpM))) : LaurentSeries κ) =
      intSeriesC κ (PowerSeries.C (((M / p : ℕ) : ℤ) ^ cN) * pf) / intSeriesC κ (PowerSeries.C (((M / p : ℕ) : ℤ) ^ cN) * pg) := by
    rw [pinR (σ b) yc hyc, intSeriesC_mul, intSeriesC_mul, mul_div_mul_left _ _ hC]
    exact DiaRedQ.coeffMap_eq_div p hyc hcg _ hgκ

  have law := hlaw.coe_apply_eq γ₀ hF hG hF₁ hG₁ hF₁s hG₁s hG0 rc
  apply Subtype.ext
  rw [law, rb]

end DiaRead
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le.DiaRedU"

end DiaRed
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le.DiaRedU"

p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC" in open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve.XHDRLevel in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by
  intro e P
  letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  haveI hne : Nonempty (Scheme.Opens.toScheme
      ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))) :=
    𝔛.Mfib_chart_nonempty A hA ρ hρ

  obtain ⟨σ, hσ⟩ :=
    ModularCurve.exists_algEquiv_chartAlgFin_gammaH_infSubgroup_forall_coeffEmb_eq_diamondAutHBar_symm p M H hpM hj e
  have hchart := ModularCurve.XHDRModelAtP.iotaFin_comp_dia0_hom_eq_spec_map_comp_iotaFin p M H hpM hpM2 hHp hj 𝔛 e σ hσ

  have pinR : ∀ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) →
      ((DiaRed.readFin (𝔛.Mfib A hA ρ hρ) (𝔛.efib A hA ρ hρ) b : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) :
          LaurentSeries (ResidueField ↥A)) = coeffMap (algebraMap (R p) (ResidueField ↥A)) y := by
    intro b y hy
    have hlift : coeffMap A.subtype (coeffMap ρ y) =
        coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) := by
      rw [coeffMap_coeffMap, hρ, ← hy, coeffEmb, coeffMap_coeffMap]
      exact coeffMap_congr (IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ)) y
    have := 𝔛.Mfib_pin A hA ρ hρ b (coeffMap ρ y) hlift
    rw [coeffMap_coeffMap] at this
    exact this

  obtain ⟨h, hh⟩ := DiaRed.placeOfPoint_fibreMap_eq_smul (𝔛.Mfib A hA ρ hρ) (𝔛.efib A hA ρ hρ) (𝔛.hefib A hA ρ hρ)
    (𝔛.dia0 e) (𝔛.dia0_over e) σ hchart
    (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e)).symm
    (fun b => (AlgEquiv.symm_apply_eq _).mpr
      (DiaRed.diamondActionModL_readFin_sigma (𝔛.Mfib A hA ρ hρ) (𝔛.efib A hA ρ hρ) hpM2 pinR e σ hσ b).symm) P
  rw [AlgEquiv.symm_symm] at hh
  exact ⟨h, hh⟩

#print axioms solution

end
end S_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le (solution)
