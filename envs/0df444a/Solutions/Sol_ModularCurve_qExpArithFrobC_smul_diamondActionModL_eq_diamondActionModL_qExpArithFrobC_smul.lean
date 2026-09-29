-- Prove2me | solution 1 for ModularCurve.qExpArithFrobC_smul_diamondActionModL_eq_diamondActionModL_qExpArithFrobC_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/18977adb-3912-517d-ab7a-a62b4c1d6543

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpArithFrobC_smul_diamondActionModL_eq_diamondActionModL_qExpArithFrobC_smul
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open ModularCurve ModularForm UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Pointwise

namespace DiaBCPen12

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

end DiaBCPen12
p2m_reactivate "P2MW.S_ModularCurve_qExpArithFrobC_smul_diamondActionModL_eq_diamondActionModL_qExpArithFrobC_smul.DiaBCPen12"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
open DiaBCPen12 in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (H' : Subgroup (ZMod N)ˣ)
    (γ : CongruenceSubgroup.Gamma0 N) (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) :
    ModularCurve.qExpArithFrobC p K (CohCarrier.GammaH N H') • (ModularCurve.diamondActionModL K N H' γ x) =
      ModularCurve.diamondActionModL K N H' γ (ModularCurve.qExpArithFrobC p K (CohCarrier.GammaH N H') • x) := by
  classical
  have hNK : (N : K) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff K p N).mp h)
  have hρ : ModularCurve.IsDiamondPullbackModL K N H' (ModularCurve.diamondActionModL K N H') :=
    ModularCurve.isDiamondPullbackModL_diamondActionModL (ModularCurve.exists_isDiamondPullbackModL_of_isAlgClosed K N hNK H')
  have hMc : ∀ c : ℕ, intSeriesC K (PowerSeries.C ((N : ℤ) ^ c)) ≠ 0 := fun c => by
    rw [intSeriesC_C, Int.cast_pow, Int.cast_natCast]
    exact HahnSeries.C_ne_zero (pow_ne_zero _ hNK)

  set ι : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) →+* ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) :=
    MulSemiringAction.toRingHom (AlgebraicCurve.SemilinearAut K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ModularCurve.qExpArithFrobC p K (CohCarrier.GammaH N H')) with hιdef
  have hιapp : ∀ y : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')), ι y = ModularCurve.qExpArithFrobC p K (CohCarrier.GammaH N H') • y := fun y => rfl
  have hι : ∀ y : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')), ((ι y : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) : LaurentSeries K) = ModularCurve.coeffMap (frobenius K p) (y : LaurentSeries K) :=
    fun y => ModularCurve.coe_qExpArithFrobC_smul p K (CohCarrier.GammaH N H') y
  have hτ : ∀ q : PowerSeries ℤ, ModularCurve.coeffMap (frobenius K p) (intSeriesC K q) = intSeriesC K q :=
    fun q => ModularCurve.coeffMap_intSeriesC (frobenius K p) q
  have hιalg : ∀ c : K, ι (algebraMap K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) c) = algebraMap K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) (c ^ p) := by
    intro c
    rw [hιapp, AlgebraicCurve.SemilinearAut.smul_def, AlgebraicCurve.SemilinearAut.commutes, ModularCurve.baseAut_qExpArithFrobC_apply]

  show ι (ModularCurve.diamondActionModL K N H' γ x) = ModularCurve.diamondActionModL K N H' γ (ι x)
  obtain ⟨x, hx⟩ := x
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨w, a, b, pa, pb, ha, hb, hb0, rfl⟩ := hy
      obtain ⟨c, F, G, F₁, G₁, pF, pG, hF, hG, hF₁, hG₁, hFs, hGs, hF₁s, hG₁s⟩ :=
        exists_integral_pair₂ a b ha hb (γ : SL(2, ℤ)) γ.2
      have hG0 : intSeriesC K pG ≠ 0 := intSeriesC_ne_zero_of_pair K hNK b hb hb0 _ γ.2 G hG hGs
      have hxk : ((⟨intSeriesC K pa / intSeriesC K pb, div_mem_qExpFunctionFieldC a b ha hb hb0⟩ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) : LaurentSeries K) =
          intSeriesC K (PowerSeries.C ((N : ℤ) ^ c) * pa) / intSeriesC K (PowerSeries.C ((N : ℤ) ^ c) * pb) := by
        show intSeriesC K pa / intSeriesC K pb = _
        rw [intSeriesC_mul, intSeriesC_mul, mul_div_mul_left _ _ (hMc c)]

      have hιx : ι ⟨intSeriesC K pa / intSeriesC K pb, div_mem_qExpFunctionFieldC a b ha hb hb0⟩ =
          ⟨intSeriesC K pa / intSeriesC K pb, div_mem_qExpFunctionFieldC a b ha hb hb0⟩ := by
        apply Subtype.ext
        rw [hι]
        show ModularCurve.coeffMap (frobenius K p) (intSeriesC K pa / intSeriesC K pb) = intSeriesC K pa / intSeriesC K pb
        rw [map_div₀, hτ, hτ]
      have hL := hρ γ w F G F₁ G₁ pF pG _ _ hF hG hF₁ hG₁ hF₁s hG₁s hG0 _ hxk
      apply Subtype.ext
      rw [hιx, hι, hL, map_div₀, hτ, hτ]
  | algebraMap c =>
      have : (⟨algebraMap K (LaurentSeries K) c, IntermediateField.algebraMap_mem _ c⟩ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) = algebraMap K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) c := rfl
      rw [this, AlgEquiv.commutes, hιalg, AlgEquiv.commutes]
  | add x y hx hy ihx ihy =>
      show ι (ModularCurve.diamondActionModL K N H' γ (⟨x, hx⟩ + ⟨y, hy⟩)) = ModularCurve.diamondActionModL K N H' γ (ι (⟨x, hx⟩ + ⟨y, hy⟩))
      rw [map_add, map_add, map_add, map_add, ihx, ihy]
  | inv x hx ih =>
      show ι (ModularCurve.diamondActionModL K N H' γ (⟨x, hx⟩⁻¹)) = ModularCurve.diamondActionModL K N H' γ (ι (⟨x, hx⟩⁻¹))
      rw [map_inv₀, map_inv₀, map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
      show ι (ModularCurve.diamondActionModL K N H' γ (⟨x, hx⟩ * ⟨y, hy⟩)) = ModularCurve.diamondActionModL K N H' γ (ι (⟨x, hx⟩ * ⟨y, hy⟩))
      rw [map_mul, map_mul, map_mul, map_mul, ihx, ihy]

end
end S_ModularCurve_qExpArithFrobC_smul_diamondActionModL_eq_diamondActionModL_qExpArithFrobC_smul
end P2MW
export P2MW.S_ModularCurve_qExpArithFrobC_smul_diamondActionModL_eq_diamondActionModL_qExpArithFrobC_smul (solution)
