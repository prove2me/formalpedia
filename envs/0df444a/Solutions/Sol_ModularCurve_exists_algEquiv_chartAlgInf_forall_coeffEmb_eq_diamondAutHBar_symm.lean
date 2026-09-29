-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/48f898f9-fba9-5794-bf06-0abd5721fdad

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_TateFormal
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd CohCarrier.frickeH1L_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open ModularCurve ModularForm UpperHalfPlane CongruenceSubgroup HahnSeries
open scoped MatrixGroups ModularForm Pointwise

namespace SigRes

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
        SlashAction.slash_one, smul_smul, smul_smul, smul_smul, _root_.pow_add]
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
    rwa [← mul_assoc, ← map_mul, ← _root_.pow_add, add_comm] at this
  · have := iF c₁ G₁ _ hG₁
    rwa [← mul_assoc, ← map_mul, ← _root_.pow_add] at this
  · rw [sF, hFs, smul_smul, ← _root_.pow_add, add_comm]
  · rw [sF, hGs, smul_smul, ← _root_.pow_add]
  · rw [sF, sF, hF₁s, ModularForm.SL_smul_slash]
  · rw [sF, sF, hG₁s, ModularForm.SL_smul_slash]

theorem intSeriesC_sub (K : Type*) [Field K] (q q' : PowerSeries ℤ) :
    intSeriesC K (q - q') = intSeriesC K q - intSeriesC K q' := by
  simp [intSeriesC]

theorem intSeriesC_C (K : Type*) [Field K] (z : ℤ) : intSeriesC K (PowerSeries.C z) = HahnSeries.C (z : K) := by
  rw [intSeriesC, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C]

end SigRes
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm.SigRes"

namespace SigRes

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

local notation "Qb" => AlgebraicClosure ℚ

theorem hstrict : (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
  one_mem_strictPeriods

theorem exists_apply_coeffEmb_eq {d : (ZMod M)ˣ} {σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H}
    (hσ : IsDiamondAutHBar M H d σ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M))
    (x : LaurentSeries ℚ) (hx : x ∈ xHFunctionField M H) :
    ∃ (k : ℤ) (f g : ModularForm (ΓH M H) k) (pf pg : PowerSeries ℤ),
      IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC ℚ pg ≠ 0 ∧ x = intSeriesC ℚ pf / intSeriesC ℚ pg ∧
      ∃ y : LaurentSeries ℚ, y ∈ xHFunctionField M H ∧
        ((σ ⟨coeffEmb Qb x, coeffEmb_mem_laurentBaseChange Qb hx⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb) =
          coeffEmb Qb y ∧
        coeffMap (algebraMap ℚ ℂ) y * HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ))) := by
  have hx' : x ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H) :=
    (ModularCurve.mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC (CohCarrier.GammaH M H) hstrict x).mp hx
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx'
  obtain ⟨y, hy, hσy, hyf⟩ := hσ k f g pf pg hf hg hg0 γ hγ hγd
  exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl, y, hy, hσy, hyf⟩

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact this

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = HahnSeries.ofPowerSeries ℤ ℂ (p.map (Int.castRingHom ℂ)) := by
  ext n
  rw [coeffMap_coeff, intSeriesC]
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · have h1 : ∀ (T : Type) [CommRing T] (q : PowerSeries T), (HahnSeries.ofPowerSeries ℤ T q).coeff n = 0 := by
      intro T _ q
      rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
      rintro ⟨m, hm⟩; exact hn (hm ▸ Int.natCast_nonneg m)
    rw [h1, h1, map_zero]

theorem gammaLift_apply_00 (e : (ZMod M)ˣ) :
    (((CuspForm.gammaLift M e : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = ((e⁻¹ : (ZMod M)ˣ) : ZMod M) := by
  set A : SL(2, ℤ) := (CuspForm.gammaLift M e : SL(2, ℤ)) with hA
  have h11 : ((A 1 1 : ℤ) : ZMod M) = (e : ZMod M) := by
    have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) (CuspForm.gamma0Units_gammaLift (M := M) e)
    simp only [CohCarrier.val_gamma0Units] at this
    exact this
  have h10 : ((A 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp (CuspForm.gammaLift M e).2
  have hdet : ((A 0 0 : ℤ) : ZMod M) * (e : ZMod M) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at this
    have h := congrArg (fun z : ℤ => (z : ZMod M)) this
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h
    rw [h11, h10, mul_zero, sub_zero] at h
    exact h
  calc ((A 0 0 : ℤ) : ZMod M) = ((A 0 0 : ℤ) : ZMod M) * ((e : ZMod M) * ((e⁻¹ : (ZMod M)ˣ) : ZMod M)) := by
        rw [Units.mul_inv, mul_one]
    _ = ((e⁻¹ : (ZMod M)ˣ) : ZMod M) := by rw [← mul_assoc, hdet, one_mul]

theorem gammaLift_mul_gammaLift_inv_mem (d : (ZMod M)ˣ) :
    ((CuspForm.gammaLift M d : SL(2, ℤ)) * (CuspForm.gammaLift M d⁻¹ : SL(2, ℤ))) ∈ CohCarrier.GammaH M H := by
  rw [show (CuspForm.gammaLift M d : SL(2, ℤ)) * (CuspForm.gammaLift M d⁻¹ : SL(2, ℤ)) =
      ((CuspForm.gammaLift M d * CuspForm.gammaLift M d⁻¹ : Gamma0 M) : SL(2, ℤ)) from rfl,
    CohCarrier.mem_GammaH_iff]
  refine ⟨(CuspForm.gammaLift M d * CuspForm.gammaLift M d⁻¹).2, ?_⟩
  have : (⟨((CuspForm.gammaLift M d * CuspForm.gammaLift M d⁻¹ : Gamma0 M) : SL(2, ℤ)),
      (CuspForm.gammaLift M d * CuspForm.gammaLift M d⁻¹).2⟩ : Gamma0 M) =
      CuspForm.gammaLift M d * CuspForm.gammaLift M d⁻¹ := rfl
  rw [this, map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift, mul_inv_cancel]
  exact one_mem H

theorem map_eq_smul_qExpansion_slash {k : ℤ} (g : ModularForm (ΓH M H) k) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (F : ModularForm (ΓH M H) k) {pF : PowerSeries ℤ} (hF : IsIntegralQExp F pF) (c : ℂ)
    (hFs : (⇑F : ℍ → ℂ) = c • ((⇑g : ℍ → ℂ) ∣[k] γ)) :
    pF.map (Int.castRingHom ℂ) = c • qExpansion 1 ((⇑g : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) := by
  rw [hF, hFs, show ((⇑g : ℍ → ℂ) ∣[k] γ) = ⇑(slashForm γ hγ g) from rfl,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods]
  rfl

theorem apply_apply_coeffEmb {d : (ZMod M)ˣ}
    {σ σ' : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H}
    (hσ : IsDiamondAutHBar M H d σ) (hσ' : IsDiamondAutHBar M H d⁻¹ σ')
    (x : LaurentSeries ℚ) (hx : x ∈ xHFunctionField M H) :
    σ (σ' ⟨coeffEmb Qb x, coeffEmb_mem_laurentBaseChange Qb hx⟩) =
      ⟨coeffEmb Qb x, coeffEmb_mem_laurentBaseChange Qb hx⟩ := by

  let γ' : SL(2, ℤ) := (CuspForm.gammaLift M d : SL(2, ℤ))
  let γd : SL(2, ℤ) := (CuspForm.gammaLift M d⁻¹ : SL(2, ℤ))
  have hγ' : γ' ∈ Gamma0 M := (CuspForm.gammaLift M d).2
  have hγd : γd ∈ Gamma0 M := (CuspForm.gammaLift M d⁻¹).2
  have hγ'00 : ((γ' 0 0 : ℤ) : ZMod M) = ((d⁻¹ : (ZMod M)ˣ) : ZMod M) := gammaLift_apply_00 d
  have hγd00 : ((γd 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    rw [show (d : ZMod M) = ((d⁻¹⁻¹ : (ZMod M)ˣ) : ZMod M) by rw [inv_inv]]; exact gammaLift_apply_00 d⁻¹

  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl, y', hy', hσ'x, hy'f⟩ := exists_apply_coeffEmb_eq hσ' γ' hγ' hγ'00 _ hx

  obtain ⟨c, F, G, F₁, G₁, pF, pG, hF, hG, -, -, hFs, hGs, -, -⟩ :=
    exists_integral_pair₂ f g hf hg γ'⁻¹ (inv_mem hγ')
  rw [inv_inv] at hFs hGs

  have hMc : ((M : ℂ) ^ c) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (NeZero.ne M))
  have hne_of_int : ∀ {k' : ℤ} (X : ModularForm (ΓH M H) k') {q : PowerSeries ℤ}, IsIntegralQExp X q →
      intSeriesC ℚ q ≠ 0 → (⇑X : ℍ → ℂ) ≠ 0 := by
    intro k' X q hX hq h0
    apply hq
    have : q = 0 := by
      apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
      rw [hX, h0, map_zero]; exact UpperHalfPlane.qExpansion_zero 1
    rw [this, intSeriesC_zero]
  have hint_of_ne : ∀ {k' : ℤ} (X : ModularForm (ΓH M H) k') {q : PowerSeries ℤ}, IsIntegralQExp X q →
      (⇑X : ℍ → ℂ) ≠ 0 → intSeriesC ℚ q ≠ 0 := by
    intro k' X q hX hXne h0
    apply hXne
    have hq : q = 0 := by
      apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
      have : HahnSeries.ofPowerSeries ℤ ℚ (q.map (Int.castRingHom ℚ)) = 0 := h0
      rw [map_zero]
      exact HahnSeries.ofPowerSeries_injective (this.trans (map_zero _).symm)
    have : UpperHalfPlane.qExpansion 1 ⇑X = 0 := by rw [← hX, hq, map_zero]
    have hX0 : X = 0 := (ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods X).mp this
    rw [hX0]; rfl
  have hgne : (⇑g : ℍ → ℂ) ≠ 0 := hne_of_int g hg hg0
  have hG0fun : (⇑G : ℍ → ℂ) ≠ 0 := by
    rw [hGs]
    intro h0
    have h1 : ((⇑g : ℍ → ℂ) ∣[k] γ') = 0 := (smul_eq_zero.mp h0).resolve_left hMc
    apply hgne
    rw [show (⇑g : ℍ → ℂ) = (((⇑g : ℍ → ℂ) ∣[k] γ') ∣[k] γ'⁻¹) by
      rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one], h1, SlashAction.zero_slash]
  have hpG0 : intSeriesC ℚ pG ≠ 0 := hint_of_ne G hG hG0fun
  have hy'eq : y' = intSeriesC ℚ pF / intSeriesC ℚ pG := by
    rw [eq_div_iff hpG0]
    apply coeffMap_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    rw [map_mul, coeffMap_intSeriesC, coeffMap_intSeriesC, map_eq_smul_qExpansion_slash g γ' hγ' G hG _ hGs,
      map_eq_smul_qExpansion_slash f γ' hγ' F hF _ hFs, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul,
      map_mul, map_mul, HahnSeries.ofPowerSeries_C, ← hy'f]
    ring

  obtain ⟨y'', hy'', hσy, hy''f⟩ := hσ k F G pF pG hF hG hpG0 γd hγd hγd00
  have hprod : (γ' * γd) ∈ CohCarrier.GammaH M H := gammaLift_mul_gammaLift_inv_mem d
  have hslash : ∀ {k' : ℤ} (X : ModularForm (ΓH M H) k'), ((⇑X : ℍ → ℂ) ∣[k'] (γ' * γd)) = ⇑X := by
    intro k' X
    have := SlashInvariantFormClass.slash_action_eq X (((γ' * γd : SL(2, ℤ))) : GL (Fin 2) ℝ) ⟨_, hprod, rfl⟩
    exact this
  have hGγ : ((⇑G : ℍ → ℂ) ∣[k] (γd : GL (Fin 2) ℝ)) = ((M : ℂ) ^ c) • (⇑g : ℍ → ℂ) := by
    show ((⇑G : ℍ → ℂ) ∣[k] γd) = _
    rw [hGs, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, hslash]
  have hFγ : ((⇑F : ℍ → ℂ) ∣[k] (γd : GL (Fin 2) ℝ)) = ((M : ℂ) ^ c) • (⇑f : ℍ → ℂ) := by
    show ((⇑F : ℍ → ℂ) ∣[k] γd) = _
    rw [hFs, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, hslash]
  have hy''eq : y'' = intSeriesC ℚ pf / intSeriesC ℚ pg := by
    rw [eq_div_iff hg0]
    apply coeffMap_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    have hC : (HahnSeries.C ((M : ℂ) ^ c) : LaurentSeries ℂ) ≠ 0 := HahnSeries.C_ne_zero hMc
    apply mul_left_cancel₀ hC
    rw [map_mul, coeffMap_intSeriesC, coeffMap_intSeriesC, hg, hf]
    rw [hGγ, hFγ, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul,
      map_mul, map_mul, HahnSeries.ofPowerSeries_C] at hy''f
    rw [← hy''f]
    ring

  have h1 : σ' ⟨coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange Qb hx⟩ =
      ⟨coeffEmb Qb (intSeriesC ℚ pF / intSeriesC ℚ pG),
        coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC F G hF hG hpG0)⟩ :=
    Subtype.ext (by rw [hσ'x, hy'eq])
  rw [h1]
  apply Subtype.ext
  rw [hσy, hy''eq]

section LevelOne
open EisensteinSeries

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

theorem isIntegralQExp_E6 : IsIntegralQExp (E₆ : ℍ → ℂ) eisenstein6 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein6, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 6 = 1 / 42 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

variable (Γ : Subgroup SL(2, ℤ))

def e4cube : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) ((E₄.pow 3).mcast (by norm_num))

def delta : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

def e4sqe6neg : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 14 :=
  restrictForm (Subgroup.map_le_range _ Γ) ((-((E₄.pow 2).mul E₆)).mcast (by norm_num))

theorem isIntegralQExp_e4cube : IsIntegralQExp (e4cube Γ : ℍ → ℂ) (eisenstein4 ^ 3) := by
  rw [IsIntegralQExp, e4cube, coe_restrictForm, map_pow, isIntegralQExp_E4,
    ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem coe_delta : (delta Γ : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem isIntegralQExp_delta :
    IsIntegralQExp (delta Γ : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) := by
  rw [IsIntegralQExp, coe_delta]
  exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem isIntegralQExp_e4sqe6neg :
    IsIntegralQExp (e4sqe6neg Γ : ℍ → ℂ) (-(eisenstein4 ^ 2 * eisenstein6)) := by
  rw [IsIntegralQExp, e4sqe6neg, coe_restrictForm, ModularForm.qExpansion_mcast, map_neg, map_mul, map_pow,
    isIntegralQExp_E4, isIntegralQExp_E6,
    ModularForm.coe_neg, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_SL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem slash_eq_of_levelOne {k : ℤ} (F : ModularForm 𝒮ℒ k) (hle : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ)
    (γ : SL(2, ℤ)) :
    ((⇑(restrictForm hle F) : ℍ → ℂ) ∣[k] γ) = ⇑(restrictForm hle F) := by
  rw [coe_restrictForm, ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq F _ ⟨γ, rfl⟩

theorem e4cube_slash (γ : SL(2, ℤ)) : ((⇑(e4cube Γ) : ℍ → ℂ) ∣[(12 : ℤ)] γ) = ⇑(e4cube Γ) :=
  slash_eq_of_levelOne Γ _ _ γ

theorem delta_slash (γ : SL(2, ℤ)) : ((⇑(delta Γ) : ℍ → ℂ) ∣[(12 : ℤ)] γ) = ⇑(delta Γ) :=
  slash_eq_of_levelOne Γ _ _ γ

theorem e4sqe6neg_slash (γ : SL(2, ℤ)) : ((⇑(e4sqe6neg Γ) : ℍ → ℂ) ∣[(14 : ℤ)] γ) = ⇑(e4sqe6neg Γ) :=
  slash_eq_of_levelOne Γ _ _ γ

end LevelOne
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm.SigRes"

section Series
variable (K : Type*) [Field K]
theorem intSeriesC_delta_ne_zero : intSeriesC K (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  have h2 : (HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem intSeriesC_neg (q : PowerSeries ℤ) : intSeriesC K (-q) = -intSeriesC K q := by
  simp [intSeriesC]

theorem intSeriesC_pow (q : PowerSeries ℤ) (n : ℕ) : intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  simp [intSeriesC]

theorem jqModC_mul_delta :
    jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

end Series
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm.SigRes"

theorem exists_algHom_of_rational (ψ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H)
    (key : ∀ x : xHFunctionField M H, ∃ y : xHFunctionField M H,
      coeffEmb Qb ((y : xHFunctionField M H) : LaurentSeries ℚ) =
        ((ψ ⟨coeffEmb Qb (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb x.2⟩ : xHFunctionFieldBar M H) :
          LaurentSeries Qb)) :
    ∃ τ : xHFunctionField M H →ₐ[ℚ] xHFunctionField M H, ∀ x : xHFunctionField M H,
      coeffEmb Qb ((τ x : xHFunctionField M H) : LaurentSeries ℚ) =
        ((ψ ⟨coeffEmb Qb (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb x.2⟩ : xHFunctionFieldBar M H) :
          LaurentSeries Qb) := by
  choose τf hτf using key
  have hinj : Function.Injective (fun z : xHFunctionField M H => coeffEmb Qb (z : LaurentSeries ℚ)) := by
    intro a b h
    apply Subtype.ext
    exact (coeffEmb Qb).injective h
  refine ⟨{ toFun := τf, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_, commutes' := ?_ }, hτf⟩
  · apply hinj
    show coeffEmb Qb ((τf 1 : xHFunctionField M H) : LaurentSeries ℚ) = coeffEmb Qb ((1 : xHFunctionField M H) : LaurentSeries ℚ)
    rw [hτf]
    have : (⟨coeffEmb Qb ((1 : xHFunctionField M H) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (1 : xHFunctionField M H).2⟩ :
        xHFunctionFieldBar M H) = 1 := Subtype.ext (by simp)
    rw [this, map_one]; simp
  · intro a b
    apply hinj
    show coeffEmb Qb ((τf (a * b) : xHFunctionField M H) : LaurentSeries ℚ) =
      coeffEmb Qb (((τf a * τf b : xHFunctionField M H)) : LaurentSeries ℚ)
    have : (⟨coeffEmb Qb ((a * b : xHFunctionField M H) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (a * b).2⟩ :
        xHFunctionFieldBar M H) =
        ⟨coeffEmb Qb (a : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb a.2⟩ *
          ⟨coeffEmb Qb (b : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb b.2⟩ :=
      Subtype.ext (by simp)
    rw [hτf, this, map_mul, MulMemClass.coe_mul,
      show ((τf a * τf b : xHFunctionField M H) : LaurentSeries ℚ) = (τf a : LaurentSeries ℚ) * (τf b : LaurentSeries ℚ) from rfl,
      map_mul, hτf, hτf]
  · apply hinj
    show coeffEmb Qb ((τf 0 : xHFunctionField M H) : LaurentSeries ℚ) = coeffEmb Qb ((0 : xHFunctionField M H) : LaurentSeries ℚ)
    rw [hτf]
    have : (⟨coeffEmb Qb ((0 : xHFunctionField M H) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (0 : xHFunctionField M H).2⟩ :
        xHFunctionFieldBar M H) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]; simp
  · intro a b
    apply hinj
    show coeffEmb Qb ((τf (a + b) : xHFunctionField M H) : LaurentSeries ℚ) =
      coeffEmb Qb (((τf a + τf b : xHFunctionField M H)) : LaurentSeries ℚ)
    have : (⟨coeffEmb Qb ((a + b : xHFunctionField M H) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (a + b).2⟩ :
        xHFunctionFieldBar M H) =
        ⟨coeffEmb Qb (a : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb a.2⟩ +
          ⟨coeffEmb Qb (b : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb b.2⟩ :=
      Subtype.ext (by simp)
    rw [hτf, this, map_add, AddMemClass.coe_add,
      show ((τf a + τf b : xHFunctionField M H) : LaurentSeries ℚ) = (τf a : LaurentSeries ℚ) + (τf b : LaurentSeries ℚ) from rfl,
      map_add, hτf, hτf]
  · intro c
    apply hinj
    show coeffEmb Qb ((τf (algebraMap ℚ (xHFunctionField M H) c) : xHFunctionField M H) : LaurentSeries ℚ) =
      coeffEmb Qb ((algebraMap ℚ (xHFunctionField M H) c : xHFunctionField M H) : LaurentSeries ℚ)
    have hcoe : ((algebraMap ℚ (xHFunctionField M H) c : xHFunctionField M H) : LaurentSeries ℚ) =
        algebraMap ℚ (LaurentSeries ℚ) c := by simp
    have hce : coeffEmb Qb (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap Qb (LaurentSeries Qb) (algebraMap ℚ Qb c) := by
      rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]
    have hbar : ∀ z : Qb, ((algebraMap Qb (xHFunctionFieldBar M H) z : xHFunctionFieldBar M H) : LaurentSeries Qb) =
        algebraMap Qb (LaurentSeries Qb) z := fun z => rfl
    have : (⟨coeffEmb Qb ((algebraMap ℚ (xHFunctionField M H) c : xHFunctionField M H) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange Qb (algebraMap ℚ (xHFunctionField M H) c).2⟩ : xHFunctionFieldBar M H) =
        algebraMap Qb (xHFunctionFieldBar M H) (algebraMap ℚ Qb c) := by
      apply Subtype.ext
      rw [hbar]
      show coeffEmb Qb _ = _
      rw [hcoe, hce]
    rw [hτf, this, AlgEquiv.commutes, hbar, hcoe, hce]

theorem apply_coeffEmb_jqModC {d : (ZMod M)ˣ} {σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H}
    (hσ : IsDiamondAutHBar M H d σ) (hjF : jqModC ℚ ∈ xHFunctionField M H) :
    σ ⟨coeffEmb Qb (jqModC ℚ), coeffEmb_mem_laurentBaseChange Qb hjF⟩ =
      ⟨coeffEmb Qb (jqModC ℚ), coeffEmb_mem_laurentBaseChange Qb hjF⟩ := by
  let γd : SL(2, ℤ) := (CuspForm.gammaLift M d⁻¹ : SL(2, ℤ))
  have hγd : γd ∈ Gamma0 M := (CuspForm.gammaLift M d⁻¹).2
  have hγd00 : ((γd 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    rw [show (d : ZMod M) = ((d⁻¹⁻¹ : (ZMod M)ˣ) : ZMod M) by rw [inv_inv]]; exact gammaLift_apply_00 d⁻¹
  have hΔ0 : intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit) ≠ 0 := intSeriesC_delta_ne_zero ℚ
  obtain ⟨y, hy, hσy, hyf⟩ := hσ 12 (e4cube (CohCarrier.GammaH M H)) (delta (CohCarrier.GammaH M H))
    (eisenstein4 ^ 3) (PowerSeries.X * dedekindEtaUnit) (isIntegralQExp_e4cube _) (isIntegralQExp_delta _) hΔ0 γd hγd hγd00
  have hyj : y = jqModC ℚ := by
    have h1 : y * intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit) = intSeriesC ℚ (eisenstein4 ^ 3) := by
      apply coeffMap_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
      rw [map_mul, coeffMap_intSeriesC, coeffMap_intSeriesC, (isIntegralQExp_delta (CohCarrier.GammaH M H)),
        (isIntegralQExp_e4cube (CohCarrier.GammaH M H))]
      have e1 : ((⇑(delta (CohCarrier.GammaH M H)) : ℍ → ℂ) ∣[(12 : ℤ)] (γd : GL (Fin 2) ℝ)) = ⇑(delta (CohCarrier.GammaH M H)) :=
        delta_slash _ γd
      have e2 : ((⇑(e4cube (CohCarrier.GammaH M H)) : ℍ → ℂ) ∣[(12 : ℤ)] (γd : GL (Fin 2) ℝ)) = ⇑(e4cube (CohCarrier.GammaH M H)) :=
        e4cube_slash _ γd
      rw [e1, e2] at hyf
      exact hyf
    rw [← jqModC_mul_delta ℚ] at h1
    exact mul_right_cancel₀ hΔ0 h1
  have hpres : intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit) = jqModC ℚ := by
    rw [eq_comm, eq_div_iff hΔ0, jqModC_mul_delta]
  have : (⟨coeffEmb Qb (jqModC ℚ), coeffEmb_mem_laurentBaseChange Qb hjF⟩ : xHFunctionFieldBar M H) =
      ⟨coeffEmb Qb (intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit)),
        coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC _ _ (isIntegralQExp_e4cube _) (isIntegralQExp_delta _) hΔ0)⟩ :=
    Subtype.ext (by show coeffEmb Qb (jqModC ℚ) = coeffEmb Qb (intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit)); rw [hpres])
  rw [this]
  apply Subtype.ext
  rw [hσy, hyj]
  show coeffEmb Qb (jqModC ℚ) = coeffEmb Qb _
  rw [hpres]

theorem exists_algHom_coeffEmb_eq_symm {d : (ZMod M)ˣ}
    {σ σ' : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H}
    (hσ : IsDiamondAutHBar M H d σ) (hσ' : IsDiamondAutHBar M H d⁻¹ σ') :
    ∃ τ : xHFunctionField M H →ₐ[ℚ] xHFunctionField M H, ∀ x : xHFunctionField M H,
      coeffEmb Qb ((τ x : xHFunctionField M H) : LaurentSeries ℚ) =
        ((σ.symm ⟨coeffEmb Qb (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb x.2⟩ : xHFunctionFieldBar M H) :
          LaurentSeries Qb) := by

  have key : ∀ x : xHFunctionField M H, ∃ y : xHFunctionField M H,
      coeffEmb Qb ((y : xHFunctionField M H) : LaurentSeries ℚ) =
        ((σ.symm ⟨coeffEmb Qb (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb x.2⟩ : xHFunctionFieldBar M H) :
          LaurentSeries Qb) := by
    intro x
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hxeq, y, hy, hσ'x, -⟩ :=
      exists_apply_coeffEmb_eq hσ' _ (CuspForm.gammaLift M d).2 (gammaLift_apply_00 d) (x : LaurentSeries ℚ) x.2
    refine ⟨⟨y, hy⟩, ?_⟩
    have hB := apply_apply_coeffEmb hσ hσ' (x : LaurentSeries ℚ) x.2
    have : σ.symm ⟨coeffEmb Qb (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb x.2⟩ =
        σ' ⟨coeffEmb Qb (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb x.2⟩ := by
      rw [AlgEquiv.symm_apply_eq, hB]
    rw [this]
    show coeffEmb Qb y = _
    rw [← hσ'x]
  choose τf hτf using key
  have hinj : Function.Injective (fun z : xHFunctionField M H => coeffEmb Qb (z : LaurentSeries ℚ)) := by
    intro a b h
    apply Subtype.ext
    exact (coeffEmb Qb).injective h
  refine ⟨{ toFun := τf, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_, commutes' := ?_ }, hτf⟩
  · apply hinj
    show coeffEmb Qb ((τf 1 : xHFunctionField M H) : LaurentSeries ℚ) = coeffEmb Qb ((1 : xHFunctionField M H) : LaurentSeries ℚ)
    rw [hτf]
    have : (⟨coeffEmb Qb ((1 : xHFunctionField M H) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (1 : xHFunctionField M H).2⟩ :
        xHFunctionFieldBar M H) = 1 := Subtype.ext (by simp)
    rw [this, map_one]; simp
  · intro a b
    apply hinj
    show coeffEmb Qb ((τf (a * b) : xHFunctionField M H) : LaurentSeries ℚ) =
      coeffEmb Qb (((τf a * τf b : xHFunctionField M H)) : LaurentSeries ℚ)
    have : (⟨coeffEmb Qb ((a * b : xHFunctionField M H) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (a * b).2⟩ :
        xHFunctionFieldBar M H) =
        ⟨coeffEmb Qb (a : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb a.2⟩ *
          ⟨coeffEmb Qb (b : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb b.2⟩ :=
      Subtype.ext (by simp)
    rw [hτf, this, map_mul, MulMemClass.coe_mul,
      show ((τf a * τf b : xHFunctionField M H) : LaurentSeries ℚ) = (τf a : LaurentSeries ℚ) * (τf b : LaurentSeries ℚ) from rfl,
      map_mul, hτf, hτf]
  · apply hinj
    show coeffEmb Qb ((τf 0 : xHFunctionField M H) : LaurentSeries ℚ) = coeffEmb Qb ((0 : xHFunctionField M H) : LaurentSeries ℚ)
    rw [hτf]
    have : (⟨coeffEmb Qb ((0 : xHFunctionField M H) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (0 : xHFunctionField M H).2⟩ :
        xHFunctionFieldBar M H) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]; simp
  · intro a b
    apply hinj
    show coeffEmb Qb ((τf (a + b) : xHFunctionField M H) : LaurentSeries ℚ) =
      coeffEmb Qb (((τf a + τf b : xHFunctionField M H)) : LaurentSeries ℚ)
    have : (⟨coeffEmb Qb ((a + b : xHFunctionField M H) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (a + b).2⟩ :
        xHFunctionFieldBar M H) =
        ⟨coeffEmb Qb (a : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb a.2⟩ +
          ⟨coeffEmb Qb (b : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb b.2⟩ :=
      Subtype.ext (by simp)
    rw [hτf, this, map_add, AddMemClass.coe_add,
      show ((τf a + τf b : xHFunctionField M H) : LaurentSeries ℚ) = (τf a : LaurentSeries ℚ) + (τf b : LaurentSeries ℚ) from rfl,
      map_add, hτf, hτf]
  · intro c
    apply hinj
    show coeffEmb Qb ((τf (algebraMap ℚ (xHFunctionField M H) c) : xHFunctionField M H) : LaurentSeries ℚ) =
      coeffEmb Qb ((algebraMap ℚ (xHFunctionField M H) c : xHFunctionField M H) : LaurentSeries ℚ)
    have hcoe : ((algebraMap ℚ (xHFunctionField M H) c : xHFunctionField M H) : LaurentSeries ℚ) =
        algebraMap ℚ (LaurentSeries ℚ) c := by simp
    have hce : coeffEmb Qb (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap Qb (LaurentSeries Qb) (algebraMap ℚ Qb c) := by
      rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]
    have hbar : ∀ z : Qb, ((algebraMap Qb (xHFunctionFieldBar M H) z : xHFunctionFieldBar M H) : LaurentSeries Qb) =
        algebraMap Qb (LaurentSeries Qb) z := fun z => rfl
    have : (⟨coeffEmb Qb ((algebraMap ℚ (xHFunctionField M H) c : xHFunctionField M H) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange Qb (algebraMap ℚ (xHFunctionField M H) c).2⟩ : xHFunctionFieldBar M H) =
        algebraMap Qb (xHFunctionFieldBar M H) (algebraMap ℚ Qb c) := by
      apply Subtype.ext
      rw [hbar]
      show coeffEmb Qb _ = _
      rw [hcoe, hce]
    rw [hτf, this, AlgEquiv.commutes, hbar, hcoe, hce]

end SigRes
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm.SigRes"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open SigRes ModularCurve.XHDRLevel in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (d : (ZMod M)ˣ) :
    ∃ σ : ↥(chartAlgInf p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj),
      ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
        coeffEmb (AlgebraicClosure ℚ) (((σ b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) :
            LaurentSeries ℚ) =
          (((diamondAutHBar M H d).symm
              ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩
            : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
  have hin := ModularCurve.heckeDiamondInputsHAll M H
  have hσ : IsDiamondAutHBar M H d (diamondAutHBar M H d) := hin.isDiamondAutHBar d
  obtain ⟨σ', hσ'⟩ := hin.2 d⁻¹

  obtain ⟨τ, hτ⟩ := exists_algHom_coeffEmb_eq_symm hσ hσ'
  have hγd00 : (((CuspForm.gammaLift M d⁻¹ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    rw [show (d : ZMod M) = ((d⁻¹⁻¹ : (ZMod M)ˣ) : ZMod M) by rw [inv_inv]]; exact gammaLift_apply_00 d⁻¹
  obtain ⟨φ, hφ⟩ := exists_algHom_of_rational (M := M) (H := H) (diamondAutHBar M H d) (fun x => by
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hxeq, y, hy, hσx, -⟩ :=
      exists_apply_coeffEmb_eq hσ _ (CuspForm.gammaLift M d⁻¹).2 hγd00 (x : LaurentSeries ℚ) x.2
    exact ⟨⟨y, hy⟩, hσx.symm⟩)

  have hτφ : ∀ x : xHFunctionField M H, τ (φ x) = x := by
    intro x
    apply Subtype.ext
    apply (coeffEmb (AlgebraicClosure ℚ)).injective
    have h1 : (⟨coeffEmb (AlgebraicClosure ℚ) ((φ x : xHFunctionField M H) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (φ x).2⟩ : xHFunctionFieldBar M H) =
        diamondAutHBar M H d ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ := Subtype.ext (hφ x)
    rw [hτ, h1, AlgEquiv.symm_apply_apply]
  have hφτ : ∀ x : xHFunctionField M H, φ (τ x) = x := by
    intro x
    apply Subtype.ext
    apply (coeffEmb (AlgebraicClosure ℚ)).injective
    have h1 : (⟨coeffEmb (AlgebraicClosure ℚ) ((τ x : xHFunctionField M H) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (τ x).2⟩ : xHFunctionFieldBar M H) =
        (diamondAutHBar M H d).symm ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ := Subtype.ext (hτ x)
    rw [hφ, h1, AlgEquiv.apply_symm_apply]

  have hjmem : jqModC ℚ ∈ xHFunctionField M H := (jAt (ΓM M H) hj).2
  have hφj : φ (jAt (ΓM M H) hj) = jAt (ΓM M H) hj := by
    apply Subtype.ext
    apply (coeffEmb (AlgebraicClosure ℚ)).injective
    rw [hφ]
    show ((diamondAutHBar M H d) ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hjmem⟩ : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ)
    rw [apply_coeffEmb_jqModC hσ hjmem]
  have hτj : τ (jAt (ΓM M H) hj) = jAt (ΓM M H) hj := by
    conv_lhs => rw [← hφj]
    exact hτφ _

  have hstab : ∀ (ψ : xHFunctionField M H →ₐ[ℚ] xHFunctionField M H), ψ (jAt (ΓM M H) hj) = jAt (ΓM M H) hj →
      ∀ x : xHFunctionField M H, x ∈ chartAlgInf p (ΓM M H) hj → ψ x ∈ chartAlgInf p (ΓM M H) hj := by
    intro ψ hψj x hx
    have hfix : ∀ a ∈ Algebra.adjoin (R p) ({(jAt (ΓM M H) hj)⁻¹} : Set (xHFunctionField M H)), ψ a = a := by
      intro a ha
      induction ha using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact (map_inv₀ ψ _).trans (congrArg (·⁻¹) hψj)
      | algebraMap r =>
          have : algebraMap (R p) (xHFunctionField M H) r = algebraMap ℚ (xHFunctionField M H) (r : ℚ) := rfl
          rw [this, AlgHom.commutes]
      | add x y _ _ hx hy => rw [map_add, hx, hy]
      | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    let A := Algebra.adjoin (R p) ({(jAt (ΓM M H) hj)⁻¹} : Set (xHFunctionField M H))
    obtain ⟨P, hPm, hP⟩ := (show IsIntegral A x from hx)
    refine ⟨P, hPm, ?_⟩
    have hcomp : ψ.toRingHom.comp (algebraMap A (xHFunctionField M H)) = algebraMap A (xHFunctionField M H) :=
      RingHom.ext fun a => hfix a a.2
    have := Polynomial.hom_eval₂ P (algebraMap A (xHFunctionField M H)) ψ.toRingHom x
    rw [hcomp, hP, map_zero] at this
    exact this.symm

  let τO : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj) :=
    { toFun := fun b => ⟨τ b.1, hstab τ hτj b.1 b.2⟩
      map_one' := Subtype.ext (map_one τ)
      map_mul' := fun a b => Subtype.ext (map_mul τ a.1 b.1)
      map_zero' := Subtype.ext (map_zero τ)
      map_add' := fun a b => Subtype.ext (map_add τ a.1 b.1)
      commutes' := fun r => Subtype.ext (by
        show τ (algebraMap (R p) (xHFunctionField M H) r) = algebraMap (R p) (xHFunctionField M H) r
        have : algebraMap (R p) (xHFunctionField M H) r = algebraMap ℚ (xHFunctionField M H) (r : ℚ) := rfl
        rw [this, AlgHom.commutes]) }
  let φO : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj) :=
    { toFun := fun b => ⟨φ b.1, hstab φ hφj b.1 b.2⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a.1 b.1)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun a b => Subtype.ext (map_add φ a.1 b.1)
      commutes' := fun r => Subtype.ext (by
        show φ (algebraMap (R p) (xHFunctionField M H) r) = algebraMap (R p) (xHFunctionField M H) r
        have : algebraMap (R p) (xHFunctionField M H) r = algebraMap ℚ (xHFunctionField M H) (r : ℚ) := rfl
        rw [this, AlgHom.commutes]) }
  refine ⟨AlgEquiv.ofAlgHom τO φO (AlgHom.ext fun b => Subtype.ext (hτφ b.1)) (AlgHom.ext fun b => Subtype.ext (hφτ b.1)), ?_⟩
  intro b
  exact hτ b.1

end
end S_ModularCurve_exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm (solution)
