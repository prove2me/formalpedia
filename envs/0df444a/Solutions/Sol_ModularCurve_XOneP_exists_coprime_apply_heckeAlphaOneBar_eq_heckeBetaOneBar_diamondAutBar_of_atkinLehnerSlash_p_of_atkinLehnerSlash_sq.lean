-- Prove2me | solution 1 for ModularCurve.XOneP.exists_coprime_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_of_atkinLehnerSlash_p_of_atkinLehnerSlash_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/72958d77-e7ad-5e37-9a34-96cfe16cfdd2

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_coprime_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_of_atkinLehnerSlash_p_of_atkinLehnerSlash_sq

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace LEGS

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

section Group

variable {M : ℕ} {ℓ : ℕ}

abbrev ΓtSL (M : ℕ) (ℓ : ℕ) : Subgroup SL(2, ℤ) :=
  Gamma1 M ⊓ Gamma0 (M * ℓ)

abbrev Γt (M : ℕ) (ℓ : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((ΓtSL M ℓ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev Γb (M : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem T_mem_top : ModularGroup.T ∈ ΓtSL M ℓ := by
  refine Subgroup.mem_inf.mpr ⟨T_mem_Gamma1, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods_top : (1 : ℝ) ∈ (Γt M ℓ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem_top]
  exact AddSubgroup.mem_zmultiples _

theorem one_mem_strictPeriods_bot : (1 : ℝ) ∈ (Γb M).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 (M := M))]
  exact AddSubgroup.mem_zmultiples _

scoped instance [NeZero M] [NeZero ℓ] : (ΓtSL M ℓ).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact Gamma1_le_of_dvd (dvd_mul_right M ℓ)

theorem top_le_bot : ΓtSL M ℓ ≤ Gamma1 M := inf_le_left

theorem Γt_le_Γb : Γt M ℓ ≤ Γb M := Subgroup.map_mono top_le_bot

def conjMat (ℓ : ℕ) (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![δ 0 0, (ℓ : ℤ) * δ 0 1; δ 1 0 / ℓ, δ 1 1]

theorem det_conjMat (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : (conjMat ℓ δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  rcases eq_or_ne (ℓ : ℤ) 0 with h0 | h0
  · simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h0, zero_mul, Int.zero_ediv,
      mul_zero, sub_zero] at hdet ⊢
    linear_combination hdet
  · have h1 : (ℓ : ℤ) * c / ℓ = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c h0
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
    linear_combination hdet

def conjSL (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨conjMat ℓ δ, det_conjMat δ h⟩

@[scoped simp] theorem conjSL_apply_00 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : conjSL δ h 0 0 = δ 0 0 := rfl
@[scoped simp] theorem conjSL_apply_01 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) :
    conjSL δ h 0 1 = (ℓ : ℤ) * δ 0 1 := rfl
@[scoped simp] theorem conjSL_apply_10 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) :
    conjSL δ h 1 0 = δ 1 0 / ℓ := rfl
@[scoped simp] theorem conjSL_apply_11 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : conjSL δ h 1 1 = δ 1 1 := rfl

theorem dvd_of_mem_Gamma0_mul {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * ℓ)) : (ℓ : ℤ) ∣ δ 1 0 := by
  rw [Gamma0_mem] at hδ
  have : ((M * ℓ : ℕ) : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ
  exact (show (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans this

theorem conjSL_mem_Gamma0 {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL δ (dvd_of_mem_Gamma0_mul hδ) ∈ Gamma0 M := by
  rw [Gamma0_mem]
  have hd : ((M * ℓ : ℕ) : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ)
  obtain ⟨c, hc⟩ := hd
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have : (conjSL δ (dvd_of_mem_Gamma0_mul hδ)) 1 0 = M * c := by
    show δ 1 0 / ℓ = M * c
    rw [hc]; push_cast
    rw [show (M : ℤ) * ℓ * c = ℓ * (M * c) by ring]
    exact Int.mul_ediv_cancel_left _ hℓ'
  rw [this]; push_cast
  simp

theorem conjSL_apply_10_eq {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    ∃ c : ℤ, (conjSL δ (dvd_of_mem_Gamma0_mul hδ)) 1 0 = M * c := by
  have hd : ((M * ℓ : ℕ) : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ)
  obtain ⟨c, hc⟩ := hd
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  refine ⟨c, ?_⟩
  show δ 1 0 / ℓ = M * c
  rw [hc]; push_cast
  rw [show (M : ℤ) * ℓ * c = ℓ * (M * c) by ring]
  exact Int.mul_ediv_cancel_left _ hℓ'

theorem conjSL_mem_GammaH {δ : SL(2, ℤ)} (hδH : δ ∈ Gamma1 M)
    (hδ : δ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL δ (dvd_of_mem_Gamma0_mul hδ) ∈ Gamma1 M := by
  rw [Gamma1_mem] at hδH ⊢
  obtain ⟨h00, h11, -⟩ := hδH
  refine ⟨?_, ?_, Gamma0_mem.mp (conjSL_mem_Gamma0 hδ hℓ)⟩
  · rw [conjSL_apply_00]; exact h00
  · rw [conjSL_apply_11]; exact h11

theorem conj_mem_Gamma1 {γ z : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hz : z ∈ Gamma1 M) : γ * z * γ⁻¹ ∈ Gamma1 M := by
  have hz0 : z ∈ Gamma0 M := Gamma1_in_Gamma0 M hz
  have hz' : (⟨z, hz0⟩ : Gamma0 M) ∈ Gamma1' M := by
    rw [Gamma1_to_Gamma0_mem]; exact (Gamma1_mem M z).mp hz
  have hN : (Gamma1' M).Normal := by unfold Gamma1'; infer_instance
  have hc : (⟨γ, hγ⟩ * ⟨z, hz0⟩ * ⟨γ, hγ⟩⁻¹ : Gamma0 M) ∈ Gamma1' M := hN.conj_mem _ hz' ⟨γ, hγ⟩
  rw [Gamma1_to_Gamma0_mem] at hc
  exact (Gamma1_mem M _).mpr (by simpa using hc)

theorem heckeDiag_mul_mul_inv {δ : SL(2, ℤ)} (h : (ℓ : ℤ) ∣ δ 1 0) (hℓ : ℓ ≠ 0) :
    ModularForm.heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ δ *
        (ModularForm.heckeDiagMatrix ℓ)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjSL δ h) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have h10 : (conjSL δ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show δ 1 0 / ℓ = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ hℓ'
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hℓ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hc] <;> ring

theorem conj_apply_10 (γ z : SL(2, ℤ)) :
    (γ * z * γ⁻¹) 1 0 = γ 1 0 * z 0 0 * γ 1 1 + γ 1 1 * z 1 0 * γ 1 1
      - γ 1 0 * z 0 1 * γ 1 0 - γ 1 1 * z 1 1 * γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

end Group

section Compose

variable {M : ℕ} {ℓ : ℕ} [NeZero ℓ] {k : ℤ}

theorem heckeDiag_smul_heckeMatrix_smul (τ : ℍ) :
    ModularForm.heckeDiagMatrix ℓ • (ModularForm.heckeMatrix ℓ 0 • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ), ModularForm.coe_heckeMatrix_smul (NeZero.ne ℓ) 0]
  have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  field_simp
  push_cast
  ring

theorem slash_diag_diag (k : ℤ) (F : ℍ → ℂ) :
    F ∣[k] (ModularForm.heckeDiagMatrix ℓ * ModularForm.heckeMatrix ℓ 0) = ((ℓ : ℂ) ^ (k - 2)) • F := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  funext τ
  rw [SlashAction.slash_mul, ModularForm.slash_heckeMatrix_apply k (NeZero.ne ℓ) 0,
    ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ), heckeDiag_smul_heckeMatrix_smul,
    Pi.smul_apply, smul_eq_mul, show k - 2 = (k - 1) + (-1) by ring, zpow_add₀ hℓ, _root_.zpow_neg_one]
  ring

theorem real_smul_slash (k : ℤ) (r : ℝ) (F : ℍ → ℂ) (g : GL (Fin 2) ℝ) :
    ((r : ℂ) • F) ∣[k] g = (r : ℂ) • (F ∣[k] g) := by
  rw [ModularForm.smul_slash, UpperHalfPlane.σ_ofReal]

omit [NeZero ℓ] in
theorem inv_pow_eq_real (k : ℤ) : ((ℓ : ℂ) ^ (k - 1))⁻¹ = ((((ℓ : ℝ) ^ (k - 1))⁻¹ : ℝ) : ℂ) := by
  push_cast; rfl

variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1)

theorem top_le_conj_bot :
    Γt M ℓ ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix ℓ)⁻¹ • Γb M := by
  rintro x ⟨δ, hδ, rfl⟩
  obtain ⟨hδH, hδ0⟩ := Subgroup.mem_inf.mp hδ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨_, conjSL_mem_GammaH hδH hδ0 (NeZero.ne ℓ),
    (heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hδ0) (NeZero.ne ℓ)).symm⟩

def levelRaise (f : ModularForm (Γb M) k) : ModularForm (Γt M ℓ) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ •
    restrictForm top_le_conj_bot (ModularForm.translate f (ModularForm.heckeDiagMatrix ℓ))

theorem levelRaise_apply (f : ModularForm (Γb M) k) (τ : ℍ) :
    levelRaise (ℓ := ℓ) f τ = f (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  show ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] ModularForm.heckeDiagMatrix ℓ) τ) = _
  rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]

theorem coe_levelRaise (f : ModularForm (Γb M) k) :
    ⇑(levelRaise (ℓ := ℓ) f) = fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ) :=
  funext (levelRaise_apply f)

theorem coe_levelRaise_eq_smul_slash (f : ModularForm (Γb M) k) :
    ⇑(levelRaise (ℓ := ℓ) f) = ((ℓ : ℂ) ^ (k - 1))⁻¹ • (⇑f ∣[k] ModularForm.heckeDiagMatrix ℓ) := rfl

end Compose

section QExp

variable {M : ℕ} {ℓ : ℕ}

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γt M ℓ) k₁) (g : ModularForm (Γt M ℓ) k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_top]

theorem qC_add {k : ℤ} (f g : ModularForm (Γt M ℓ) k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_top f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (Γt M ℓ) k) : qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_top c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (Γt M ℓ) k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_top f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γt M ℓ) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_top f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_eq_zero_iff_bot {k : ℤ} (f : ModularForm (Γb M) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_bot f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem ιC_injective : Function.Injective ιC :=
  RingHom.injective _

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem ιC_C (c : ℚ) : ιC (HahnSeries.C c) = HahnSeries.C (c : ℂ) := by
  rw [ιC, coeffMap]
  ext n
  simp

theorem qC_ιC_ne_zero {k : ℤ} {g : ModularForm (Γt M ℓ) k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ ιC_injective).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γt M ℓ) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ιC_ne_zero hg hg0 ((qC_eq_zero_iff g).mpr h)

theorem intSeriesC_add' {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

theorem intSeriesC_neg' {K : Type*} [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (-p) = -intSeriesC K p := by
  simp [intSeriesC]

theorem intSeriesC_C_mul (K : Type*) [Field K] (n : ℤ) (p : PowerSeries ℤ) :
    intSeriesC K (PowerSeries.C n * p) = HahnSeries.C (n : K) * intSeriesC K p := by
  rw [intSeriesC_mul, intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]

section RatioGen

variable {Γ : Subgroup SL(2, ℤ)}
  (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods)

include hΓ

theorem mul_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) (hb : b ∈ intFormRatiosC ℚ Γ) :
    a * b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf₁, hf₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos hΓ f₁ f₂).symm
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos hΓ g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]

theorem add_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) (hb : b ∈ intFormRatiosC ℚ Γ) :
    a + b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos hΓ, ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos hΓ, ModularForm.qExpansion_mul_coe one_pos hΓ]
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos hΓ g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ hg₁0 hg₂0]

theorem neg_mem_ratios {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) : -a ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  refine ⟨k, -f, g, -pf, pg, ?_, hg, hg0, ?_⟩
  · rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
    exact (ModularForm.qExpansion_neg one_pos hΓ f).symm
  · rw [intSeriesC_neg', neg_div]

omit hΓ in
theorem inv_mem_ratios {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) : a⁻¹ ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, _root_.inv_zero, ← zero_div (intSeriesC ℚ pg), ← hf0]
    exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  · refine ⟨k, g, f, pg, pf, hg, hf, hf0, ?_⟩
    rw [inv_div]

omit hΓ in
theorem coe_const_eq_smul_one (c : ℂ) :
    ((ModularForm.const c : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) =
      c • ((1 : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) := by
  funext z
  rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
    mul_one]

theorem isIntegralQExp_const (n : ℤ) :
    IsIntegralQExp ((ModularForm.const (n : ℂ) :
      ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) (PowerSeries.C n) := by
  rw [IsIntegralQExp, PowerSeries.map_C, coe_const_eq_smul_one,
    ModularForm.qExpansion_smul one_pos hΓ, ModularForm.qExpansion_one,
    PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]

theorem algebraMap_mem_ratios (c : ℚ) : algebraMap ℚ (LaurentSeries ℚ) c ∈ intFormRatiosC ℚ Γ := by
  have hden : ((c.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  refine ⟨0, ModularForm.const (c.num : ℂ), ModularForm.const (c.den : ℂ),
    PowerSeries.C (c.num : ℤ), PowerSeries.C (c.den : ℤ), isIntegralQExp_const hΓ _, ?_, ?_, ?_⟩
  · have := isIntegralQExp_const hΓ (c.den : ℤ)
    push_cast at this
    exact this
  · rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]
    exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr hden
  · rw [intSeriesC, intSeriesC, PowerSeries.map_C, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply, eq_intCast,
      eq_intCast, eq_div_iff ((map_ne_zero_iff _ HahnSeries.C_injective).mpr hden), ← map_mul]
    congr 1
    push_cast
    exact Rat.mul_den_eq_num c

def SFieldGen : IntermediateField ℚ (LaurentSeries ℚ) where
  carrier := intFormRatiosC ℚ Γ
  mul_mem' ha hb := mul_mem_ratios hΓ ha hb
  one_mem' := by simpa using algebraMap_mem_ratios hΓ 1
  add_mem' ha hb := add_mem_ratios hΓ ha hb
  zero_mem' := by simpa using algebraMap_mem_ratios hΓ 0
  algebraMap_mem' c := algebraMap_mem_ratios hΓ c
  inv_mem' a ha := inv_mem_ratios ha

theorem mem_ratios_of_mem {y : LaurentSeries ℚ} (hy : y ∈ qExpFunctionFieldC ℚ Γ) : y ∈ intFormRatiosC ℚ Γ := by
  have hle : qExpFunctionFieldC ℚ Γ ≤ SFieldGen hΓ := IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

end RatioGen

variable (M ℓ) in

abbrev S : Set (LaurentSeries ℚ) := intFormRatiosC ℚ (ΓtSL M ℓ)

theorem mem_S_of_mem {y : LaurentSeries ℚ} (hy : y ∈ x1x0FunctionFieldC ℚ M (M * ℓ)) : y ∈ S M ℓ :=
  mem_ratios_of_mem one_mem_strictPeriods_top hy

theorem mem_Sb_of_mem {y : LaurentSeries ℚ} (hy : y ∈ x1FunctionField M) :
    y ∈ intFormRatiosC ℚ (Gamma1 M) :=
  mem_ratios_of_mem one_mem_strictPeriods_bot hy

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γt M ℓ) k₁) (f₂ : ModularForm (Γt M ℓ) k₂)
    (f₃ : ModularForm (Γt M ℓ) k₃) (f₄ : ModularForm (Γt M ℓ) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (Γt M ℓ) (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
  have hcoe : (⇑D : ℍ → ℂ) = ⇑f₁ * ⇑f₂ - ⇑f₃ * ⇑f₄ := by
    rw [hD, ModularForm.coe_sub, ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul]
  have hq : qC (⇑D) = 0 := by
    have hsub := ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_top (f₁.mul f₂)
      (ModularForm.mcast hk (f₃.mul f₄))
    rw [ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul] at hsub
    rw [hcoe, qC, hsub, map_sub]
    change qC (⇑f₁ * ⇑f₂) - qC (⇑f₃ * ⇑f₄) = 0
    rw [qC_mul, qC_mul, h, sub_self]
  have hD0 : D = 0 := (qC_eq_zero_iff D).mp hq
  have : (⇑D : ℍ → ℂ) = 0 := by rw [hD0, ModularForm.coe_zero]
  rw [hcoe] at this
  exact sub_eq_zero.mp this

end QExp

section Expand

variable {M : ℕ} {ℓ : ℕ} [NeZero ℓ] {k : ℤ}

theorem coeffMap_qExpand {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T)
    (x : LaurentSeries R) : coeffMap φ (qExpand R ℓ x) = qExpand T ℓ (coeffMap φ x) := by
  ext n
  by_cases hk : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd ℓ _ hk, qExpand_coeff_of_not_dvd ℓ _ hk, map_zero]

def expandPS {R : Type*} [CommRing R] (ℓ : ℕ) (P : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => if ℓ ∣ n then PowerSeries.coeff (n / ℓ) P else 0

omit [NeZero ℓ] in
theorem coeff_expandPS {R : Type*} [CommRing R] (P : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (expandPS ℓ P) = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) P else 0 := by
  rw [expandPS, PowerSeries.coeff_mk]

theorem ofPowerSeries_expandPS {R : Type*} [CommRing R] (P : PowerSeries R) :
    ofPowerSeries ℤ R (expandPS ℓ P) = qExpand R ℓ (ofPowerSeries ℤ R P) := by
  ext m
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg hℓ0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity)]
      simp only [coeff_expandPS]
      have h1 : ((ℓ : ℤ) * j).natAbs = ℓ * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [coeff_expandPS, if_neg]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

omit [NeZero ℓ] in
theorem expandPS_map (P : PowerSeries ℤ) :
    expandPS ℓ (P.map (Int.castRingHom ℂ)) = (expandPS ℓ P).map (Int.castRingHom ℂ) := by
  ext n
  simp only [coeff_expandPS, PowerSeries.coeff_map]
  split_ifs <;> simp

theorem qExpansion_comp_heckeDiag (f : ModularForm (Γb M) k) :
    qExpansion 1 (fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ)) = expandPS ℓ (qExpansion 1 f) := by
  ext n
  rw [coeff_expandPS]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f one_mem_strictPeriods_bot (NeZero.ne ℓ) n

theorem qC_levelRaise (f : ModularForm (Γb M) k) :
    qC (levelRaise (ℓ := ℓ) f) = qExpand ℂ ℓ (qC f) := by
  rw [qC, coe_levelRaise, qExpansion_comp_heckeDiag, ofPowerSeries_expandPS, qC]

theorem isIntegralQExp_levelRaise {f : ModularForm (Γb M) k} {pf : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) : IsIntegralQExp (levelRaise (ℓ := ℓ) f) (expandPS ℓ pf) := by
  rw [IsIntegralQExp, coe_levelRaise, qExpansion_comp_heckeDiag, ← hf, expandPS_map]

theorem intSeriesC_expandPS (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (expandPS ℓ p) = qExpand K ℓ (intSeriesC K p) := by
  rw [intSeriesC, intSeriesC, ← ofPowerSeries_expandPS]
  congr 1
  ext n
  simp only [coeff_expandPS, PowerSeries.coeff_map]
  split_ifs <;> simp

end Expand

section Dia

variable {N : ℕ} {k : ℤ}

theorem le_conj_dia {S : SL(2, ℤ)} (hS : S ∈ Gamma0 N) :
    Γb N ≤ ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ S)⁻¹ • Γb N := by
  rintro x ⟨z, hz, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨_, conj_mem_Gamma1 hS hz, ?_⟩
  simp only [map_mul, map_inv]

def diaForm (S : SL(2, ℤ)) (hS : S ∈ Gamma0 N) (f : ModularForm (Γb N) k) : ModularForm (Γb N) k :=
  restrictForm (le_conj_dia hS) (ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ S))

theorem coe_diaForm (S : SL(2, ℤ)) (hS : S ∈ Gamma0 N) (f : ModularForm (Γb N) k) :
    ⇑(diaForm S hS f) = ⇑f ∣[k] S := by
  rw [ModularForm.SL_slash]; rfl

end Dia

section DiaLaw

open ModularCurve

theorem coeffMap_coeffEmb_eq_ιC (ι : AlgebraicClosure ℚ →+* ℂ) (x : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb (AlgebraicClosure ℚ) x) = ιC x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun q => by simp [eq_ratCast]) x

theorem comp_heckeDiag_ne_zero {n : ℕ} (hn : n ≠ 0) {F : UpperHalfPlane → ℂ} (hF : F ≠ 0) :
    (fun w : UpperHalfPlane => F (ModularForm.heckeDiagMatrix n • w)) ≠ 0 := by
  haveI : NeZero n := ⟨hn⟩
  intro h0
  apply hF
  funext z
  have := congrFun h0 (ModularForm.heckeMatrix n 0 • z)
  simpa [heckeDiag_smul_heckeMatrix_smul] using this

theorem qC_diaForm_ne_zero {N : ℕ} {k : ℤ} {g : ModularForm (Γb N) k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (S : SL(2, ℤ)) (hS : S ∈ Gamma0 N) : qC (⇑(diaForm S hS g)) ≠ 0 := by
  intro h0
  have h1 : diaForm S hS g = 0 := (qC_eq_zero_iff_bot _).mp h0
  have h2 : (⇑g : UpperHalfPlane → ℂ) ∣[k] S = 0 := by rw [← coe_diaForm S hS g, h1]; rfl
  have h3 : (⇑g : UpperHalfPlane → ℂ) = 0 := by
    have h4 := congrArg (fun F : UpperHalfPlane → ℂ => F ∣[k] S⁻¹) h2
    rwa [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, SlashAction.zero_slash] at h4
  have hq : qC (⇑g) = 0 := by rw [h3, qC_zero]
  exact hg0 ((map_eq_zero_iff _ ιC_injective).mp ((ιC_intSeriesC hg).trans hq))

theorem coeffMap_diamondAutBar_mul_qC (N : ℕ) [NeZero N] (ι : AlgebraicClosure ℚ →+* ℂ) {d : ℕ} (hd : Nat.Coprime d N)
    {k : ℤ} (f g : ModularForm (Γb N) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (S : SL(2, ℤ)) (hS : S ∈ Gamma0 N) (hS00 : ((S 0 0 : ℤ) : ZMod N) = (d : ZMod N)) :
    coeffMap ι ((diamondAutBar N d
        ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
        x1FunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) * qC (⇑g ∣[k] S) = qC (⇑f ∣[k] S) := by
  have hD : IsDiamondAut N d (diamondAut N d) := isDiamondAut_diamondAut (exists_isDiamondAut N hd)
  have hB : IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut N d) (diamondAutBar N d) := by
    apply isBaseChangeAutOf_baseChangeAut
    obtain ⟨τ, hτ⟩ := exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ) (x1FunctionField N) (diamondAut N d).toRingEquiv
    exact ⟨τ, hτ⟩
  have h1 := hB ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩
  have h2 := hD.2 k f g pf pg hf hg hg0 S hS hS00
  rw [show (diamondAutBar N d : x1FunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar N) = baseChangeAut (AlgebraicClosure ℚ) (diamondAut N d) from rfl] at *
  rw [h1, coeffMap_coeffEmb_eq_ιC]
  simpa [slashQExpC, qC, ModularForm.SL_slash] using h2

end DiaLaw

section MatrixId

variable {M : ℕ} {p : ℕ} [NeZero p]

theorem heckeDiag_mul_heckeDiag :
    ModularForm.heckeDiagMatrix p * ModularForm.heckeDiagMatrix p = ModularForm.heckeDiagMatrix (p ^ 2) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hp, ModularForm.val_heckeDiagMatrix hp2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring

variable (y w₀ y₂ w₂ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1) (hrel₂ : (p : ℤ) ^ 2 * w₂ - (M : ℤ) * y₂ = 1)
  (γ' δ : SL(2, ℤ)) (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w₀, -y; -(M : ℤ), (p : ℤ)])
  (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y₂; (M : ℤ), (p : ℤ) ^ 2 * w₂])

def S₁ : SL(2, ℤ) := ⟨!![1, w₀ * y₂ - (p : ℤ) * y * w₂; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def S₂ : SL(2, ℤ) :=
  ⟨!![(p : ℤ) ^ 2 * w₀ - (M : ℤ) * y, w₀ * y₂ - y * w₂; (M : ℤ) * p * (1 - p), (p : ℤ) * w₂ - (M : ℤ) * y₂], by
    rw [Matrix.det_fin_two_of]
    linear_combination ((p : ℤ) ^ 2 * w₂ - (M : ℤ) * y₂) * hrel + hrel₂⟩

end MatrixId

section SlashId

variable {M : ℕ} {p : ℕ} [NeZero p]
variable (y w₀ y₂ w₂ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1) (hrel₂ : (p : ℤ) ^ 2 * w₂ - (M : ℤ) * y₂ = 1)
  (γ' δ : SL(2, ℤ)) (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w₀, -y; -(M : ℤ), (p : ℤ)])
  (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y₂; (M : ℤ), (p : ℤ) ^ 2 * w₂])

include hrel hrel₂ hγ' hδ in

theorem matId₁ :
    ((γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix (p ^ 2) =
      ((S₁ (p := p) y w₀ y₂ w₂ : SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p *
        (ModularForm.heckeDiagMatrix p * ModularForm.heckeMatrix p 0) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have hrelR : (p : ℝ) * w₀ - (M : ℝ) * y = 1 := by exact_mod_cast hrel
  have hrel₂R : (p : ℝ) ^ 2 * w₂ - (M : ℝ) * y₂ = 1 := by exact_mod_cast hrel₂
  have e00 : γ' 0 0 = w₀ := by rw [hγ']; rfl
  have e01 : γ' 0 1 = -y := by rw [hγ']; rfl
  have e10 : γ' 1 0 = -(M : ℤ) := by rw [hγ']; rfl
  have e11 : γ' 1 1 = (p : ℤ) := by rw [hγ']; rfl
  have d00 : δ 0 0 = 1 := by rw [hδ]; rfl
  have d01 : δ 0 1 = y₂ := by rw [hδ]; rfl
  have d10 : δ 1 0 = (M : ℤ) := by rw [hδ]; rfl
  have d11 : δ 1 1 = (p : ℤ) ^ 2 * w₂ := by rw [hδ]; rfl
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hp, ModularForm.val_heckeDiagMatrix hp2,
    ModularForm.val_heckeMatrix hp]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, S₁, e00, e01, e10, e11, d00, d01, d10, d11] <;>
    (try push_cast) <;>
    (first
      | ring1
      | exact Or.inl trivial
      | (left; ring1)
      | linear_combination (p : ℝ) ^ 2 * hrelR
      | linear_combination (p : ℝ) * hrel₂R
      | linear_combination (p : ℝ) * hrelR
      | linear_combination (p : ℝ) ^ 2 * hrel₂R
      | linear_combination (-(p : ℝ) ^ 2) * hrel₂R
      | linear_combination (-(p : ℝ) ^ 2) * hrelR
      | linear_combination (-(p : ℝ)) * hrel₂R
      | linear_combination (-(p : ℝ)) * hrelR)

include hrel hrel₂ hγ' hδ in

theorem matId₂ :
    ((γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p * ModularForm.heckeDiagMatrix p *
        ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix (p ^ 2) =
      ((S₂ (p := p) y w₀ y₂ w₂ hrel hrel₂ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        (ModularForm.heckeDiagMatrix p * ModularForm.heckeMatrix p 0) *
        (ModularForm.heckeDiagMatrix p * ModularForm.heckeMatrix p 0) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have hrelR : (p : ℝ) * w₀ - (M : ℝ) * y = 1 := by exact_mod_cast hrel
  have hrel₂R : (p : ℝ) ^ 2 * w₂ - (M : ℝ) * y₂ = 1 := by exact_mod_cast hrel₂
  have e00 : γ' 0 0 = w₀ := by rw [hγ']; rfl
  have e01 : γ' 0 1 = -y := by rw [hγ']; rfl
  have e10 : γ' 1 0 = -(M : ℤ) := by rw [hγ']; rfl
  have e11 : γ' 1 1 = (p : ℤ) := by rw [hγ']; rfl
  have d00 : δ 0 0 = 1 := by rw [hδ]; rfl
  have d01 : δ 0 1 = y₂ := by rw [hδ]; rfl
  have d10 : δ 1 0 = (M : ℤ) := by rw [hδ]; rfl
  have d11 : δ 1 1 = (p : ℤ) ^ 2 * w₂ := by rw [hδ]; rfl
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hp, ModularForm.val_heckeDiagMatrix hp2,
    ModularForm.val_heckeMatrix hp]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, S₂, e00, e01, e10, e11, d00, d01, d10, d11] <;>
    (try push_cast) <;>
    (first
      | ring1
      | exact Or.inl trivial
      | (left; ring1)
      | linear_combination (p : ℝ) ^ 2 * hrelR
      | linear_combination (p : ℝ) * hrel₂R
      | linear_combination (p : ℝ) * hrelR
      | linear_combination (p : ℝ) ^ 2 * hrel₂R
      | linear_combination (-(p : ℝ) ^ 2) * hrel₂R
      | linear_combination (-(p : ℝ) ^ 2) * hrelR
      | linear_combination (-(p : ℝ)) * hrel₂R
      | linear_combination (-(p : ℝ)) * hrelR
      | linear_combination ((p : ℝ) ^ 2 * w₂ - (M : ℝ) * y₂) * hrelR + hrel₂R
      | linear_combination (p : ℝ) ^ 2 * (((p : ℝ) ^ 2 * w₂ - (M : ℝ) * y₂) * hrelR + hrel₂R))

end SlashId

section SlashConseq

variable {M : ℕ} {p : ℕ} [NeZero p]
variable (y w₀ y₂ w₂ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1) (hrel₂ : (p : ℤ) ^ 2 * w₂ - (M : ℤ) * y₂ = 1)
  (γ' δ : SL(2, ℤ)) (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w₀, -y; -(M : ℤ), (p : ℤ)])
  (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y₂; (M : ℤ), (p : ℤ) ^ 2 * w₂])

theorem apply_heckeDiag_smul (k : ℤ) {n : ℕ} (hn : n ≠ 0) (F : ℍ → ℂ) (w : ℍ) :
    F (ModularForm.heckeDiagMatrix n • w) = ((n : ℂ) ^ (k - 1))⁻¹ * (F ∣[k] ModularForm.heckeDiagMatrix n) w := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [ModularForm.slash_heckeDiagMatrix_apply k hn, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hn'), one_mul]

theorem comp_heckeDiag_eq_smul_slash (k : ℤ) (F : ℍ → ℂ) :
    (fun w : ℍ => F (ModularForm.heckeDiagMatrix p • w)) =
      ((((p : ℝ) ^ (k - 1))⁻¹ : ℝ) : ℂ) • (F ∣[k] ModularForm.heckeDiagMatrix p) := by
  funext w
  rw [apply_heckeDiag_smul k (NeZero.ne p) F w, Pi.smul_apply, smul_eq_mul]
  push_cast
  rfl

theorem zpow_book₁ (x : ℂ) (hx : x ≠ 0) (k : ℤ) :
    (x ^ (k - 1))⁻¹ * ((x ^ 2) ^ (k - 1))⁻¹ * x ^ (k - 2) * x ^ (k - 1) = (x ^ k)⁻¹ := by
  have h2 : ((x ^ 2) ^ (k - 1) : ℂ) = x ^ (2 * (k - 1)) := by
    rw [← zpow_natCast x 2, ← _root_.zpow_mul]; norm_num
  rw [h2]
  simp only [← _root_.zpow_neg, ← zpow_add₀ hx]
  congr 1; ring

theorem zpow_book₂ (x : ℂ) (hx : x ≠ 0) (k : ℤ) :
    (x ^ (k - 1))⁻¹ * (x ^ (k - 1))⁻¹ * ((x ^ 2) ^ (k - 1))⁻¹ * x ^ (k - 2) * x ^ (k - 2) = (x ^ (2 * k))⁻¹ := by
  have h2 : ((x ^ 2) ^ (k - 1) : ℂ) = x ^ (2 * (k - 1)) := by
    rw [← zpow_natCast x 2, ← _root_.zpow_mul]; norm_num
  rw [h2]
  simp only [← _root_.zpow_neg, ← zpow_add₀ hx]
  congr 1; ring

include hrel hrel₂ hγ' hδ in

theorem AL₁ (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    ((fun w : ℍ => (f ∣[k] γ') (ModularForm.heckeDiagMatrix p • w)) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z) =
      ((p : ℂ) ^ k)⁻¹ * (f ∣[k] S₁ (p := p) y w₀ y₂ w₂) (ModularForm.heckeDiagMatrix p • z) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [comp_heckeDiag_eq_smul_slash, ModularForm.SL_slash, ModularForm.SL_slash, real_smul_slash,
    ← SlashAction.slash_mul, ← SlashAction.slash_mul, ← mul_assoc, Pi.smul_apply,
    apply_heckeDiag_smul k hp2 (f ∣[k] (((γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p *
      ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ))),
    ← SlashAction.slash_mul, matId₁ y w₀ y₂ w₂ hrel hrel₂ γ' δ hγ' hδ, SlashAction.slash_mul, slash_diag_diag,
    Pi.smul_apply, SlashAction.slash_mul, ModularForm.slash_heckeDiagMatrix_apply k hp, ← ModularForm.SL_slash]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← zpow_book₁ (p : ℂ) hpC k]
  ring

include hrel hrel₂ hγ' hδ in

theorem AL₂ (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    ((fun w : ℍ => (fun w' : ℍ => (f ∣[k] γ') (ModularForm.heckeDiagMatrix p • w')) (ModularForm.heckeDiagMatrix p • w)) ∣[k] δ)
        (ModularForm.heckeDiagMatrix (p ^ 2) • z) =
      ((p : ℂ) ^ (2 * k))⁻¹ * (f ∣[k] S₂ (p := p) y w₀ y₂ w₂ hrel hrel₂) z := by
  have hp : p ≠ 0 := NeZero.ne p
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [comp_heckeDiag_eq_smul_slash k (fun w' : ℍ => (f ∣[k] γ') (ModularForm.heckeDiagMatrix p • w')),
    comp_heckeDiag_eq_smul_slash, ModularForm.SL_slash, ModularForm.SL_slash, real_smul_slash, real_smul_slash,
    real_smul_slash, ← SlashAction.slash_mul, ← SlashAction.slash_mul, ← SlashAction.slash_mul, ← mul_assoc, ← mul_assoc,
    Pi.smul_apply, Pi.smul_apply,
    apply_heckeDiag_smul k hp2 (f ∣[k] (((γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p *
      ModularForm.heckeDiagMatrix p * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ))),
    ← SlashAction.slash_mul,
    matId₂ y w₀ y₂ w₂ hrel hrel₂ γ' δ hγ' hδ, SlashAction.slash_mul, slash_diag_diag, Pi.smul_apply,
    SlashAction.slash_mul, slash_diag_diag, ← ModularForm.SL_slash]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← zpow_book₂ (p : ℂ) hpC k]
  ring

end SlashConseq

section RatioLaw

variable {N p : ℕ} [NeZero N] [NeZero p]

theorem eq_zero_of_slash_heckeDiag_eq_zero {k : ℤ} (g : ModularForm (Γt N p) k) (δ : SL(2, ℤ))
    (h : ∀ z : ℍ, ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z) = 0) : g = 0 := by
  have h1 : ((⇑g) ∣[k] δ) = 0 := by
    funext w
    have := h (ModularForm.heckeMatrix (p ^ 2) 0 • w)
    rw [heckeDiag_smul_heckeMatrix_smul] at this
    exact this
  have h2 : (⇑g : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ℍ → ℂ => F ∣[k] (δ⁻¹ : SL(2, ℤ))) h1
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, SlashAction.zero_slash] at this
    exact this
  exact DFunLike.ext' (by rw [h2, ModularForm.coe_zero])

theorem ratio_law_of_presentations {k k'' : ℤ}
    (Φ Ψ : ModularForm (Γt N p) k) (f'' g'' φ₂ ψ₂ : ModularForm (Γt N p) k'') (D₂ E₂ : ℤ) (hD₂ : D₂ ≠ 0) (hE₂ : E₂ ≠ 0)
    (δ : SL(2, ℤ))
    (hφ₂ : (⇑φ₂ : ℍ → ℂ) = (D₂ : ℂ) • (fun z : ℍ => ((⇑f'') ∣[k''] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)))
    (hψ₂ : (⇑ψ₂ : ℍ → ℂ) = (E₂ : ℂ) • (fun z : ℍ => ((⇑g'') ∣[k''] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)))
    (hΨ : qC (⇑Ψ) ≠ 0) (hg'' : qC (⇑g'') ≠ 0)
    (heq : qC (⇑Φ) / qC (⇑Ψ) = qC (⇑f'') / qC (⇑g''))
    (F G : ModularForm (Γt N p) k) (c : ℂ) (hc : c ≠ 0)
    (hF : ∀ z : ℍ, ((⇑Φ) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z) = c * F z)
    (hG : ∀ z : ℍ, ((⇑Ψ) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z) = c * G z)
    (hG0 : qC (⇑G) ≠ 0) :
    HahnSeries.C ((E₂ : ℂ) / (D₂ : ℂ)) * qC (⇑φ₂) / qC (⇑ψ₂) = qC (⇑F) / qC (⇑G) := by
  have hD₂C : (D₂ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD₂
  have hE₂C : (E₂ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hE₂

  have hprod : (⇑Φ * ⇑g'' : ℍ → ℂ) = ⇑Ψ * ⇑f'' := by
    apply mul_eq_mul_of_qC Φ g'' Ψ f'' rfl
    rw [div_eq_div_iff hΨ hg''] at heq
    rw [heq, mul_comm]

  have hpt : ∀ z : ℍ, (D₂ : ℂ) * (F z * ψ₂ z) = (E₂ : ℂ) * (G z * φ₂ z) := by
    intro z
    have hs := congrArg (fun H : ℍ → ℂ => (H ∣[k + k''] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) hprod
    rw [ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2, Pi.mul_apply, Pi.mul_apply, hF, hG] at hs
    have e1 : ((⇑f'') ∣[k''] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z) = (D₂ : ℂ)⁻¹ * φ₂ z := by
      rw [hφ₂, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hD₂C, one_mul]
    have e2 : ((⇑g'') ∣[k''] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z) = (E₂ : ℂ)⁻¹ * ψ₂ z := by
      rw [hψ₂, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hE₂C, one_mul]
    rw [e1, e2] at hs

    have hs' := congrArg (fun t => (D₂ : ℂ) * (E₂ : ℂ) * c⁻¹ * t) hs
    field_simp at hs'
    linear_combination hs'

  have hfun : ((D₂ : ℂ) • (⇑F * ⇑ψ₂) : ℍ → ℂ) = (E₂ : ℂ) • (⇑G * ⇑φ₂) := by
    funext z
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    exact hpt z
  have hq : HahnSeries.C (D₂ : ℂ) * (qC (⇑F) * qC (⇑ψ₂)) = HahnSeries.C (E₂ : ℂ) * (qC (⇑G) * qC (⇑φ₂)) := by
    have := congrArg qC hfun
    rwa [← ModularForm.coe_mul, ← ModularForm.coe_mul, qC_smul, qC_smul, ModularForm.coe_mul, ModularForm.coe_mul, qC_mul, qC_mul] at this

  have hψ₂0 : qC (⇑ψ₂) ≠ 0 := by
    intro h0
    have hz : ψ₂ = 0 := (qC_eq_zero_iff ψ₂).mp h0
    apply hg''
    rw [qC_eq_zero_iff]
    apply eq_zero_of_slash_heckeDiag_eq_zero g'' δ
    intro z
    have := congrFun hψ₂ z
    rw [hz, ModularForm.coe_zero, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hE₂C
  have hCD : (HahnSeries.C (D₂ : ℂ) : LaurentSeries ℂ) ≠ 0 := HahnSeries.C_ne_zero hD₂C
  rw [div_eq_div_iff hψ₂0 hG0, map_div₀, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hCD]
  linear_combination -hq

end RatioLaw

section TauSymm

open ModularCurve

theorem coeffMap_generator {N : ℕ} (ι : AlgebraicClosure ℚ →+* ℂ) {k : ℤ} (f g : ModularForm (Γb N) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    coeffMap ι ((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
        ↥(x1FunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) = qC (⇑f) / qC (⇑g) := by
  show coeffMap ι (coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg)) = _
  rw [coeffMap_coeffEmb_eq_ιC, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg]

theorem tau_symm_generator (p M : ℕ) [Fact p.Prime] [NeZero M] (hpM : ¬ p ∣ M)
    (ι : AlgebraicClosure ℚ →+* ℂ) (γ' : SL(2, ℤ)) (hγ'0 : γ' ∈ Gamma0 M) (hγ'p : (p : ℤ) ∣ γ' 1 1)
    (τ : ↥(x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar (M * p)))
    (hE1' : (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ.symm x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)))
    {k : ℤ} (f g : ModularForm (Γb (M * p)) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ∃ Φ Ψ : ModularForm (Γb (M * p)) k,
      ((⇑Φ : ℍ → ℂ) = fun z : ℍ => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) ∧
      ((⇑Ψ : ℍ → ℂ) = fun z : ℍ => ((⇑g) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) ∧
      qC (⇑Ψ) ≠ 0 ∧
      coeffMap ι ((τ.symm ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = qC (⇑Φ) / qC (⇑Ψ) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨Φ, hΦ⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p M hpM f γ' hγ'0 hγ'p
  obtain ⟨Ψ, hΨ⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p M hpM g γ' hγ'0 hγ'p
  have hqg : qC (⇑g) ≠ 0 := by
    rw [← ιC_intSeriesC hg]; exact (map_ne_zero_iff _ ιC_injective).mpr hg0
  have hgne : (⇑g : ℍ → ℂ) ≠ 0 := fun h => hqg (by rw [h, qC_zero])
  have hgs : (⇑g : ℍ → ℂ) ∣[k] γ' ≠ 0 := by
    intro h
    apply hgne
    have h4 := congrArg (fun F : ℍ → ℂ => F ∣[k] γ'⁻¹) h
    rwa [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, SlashAction.zero_slash] at h4
  have hΨne : qC (⇑Ψ) ≠ 0 := by
    intro h0
    have h1 : Ψ = 0 := (qC_eq_zero_iff_bot _).mp h0
    have h2 : (⇑Ψ : ℍ → ℂ) = 0 := by rw [h1]; rfl
    exact comp_heckeDiag_ne_zero hp0 hgs (hΨ ▸ h2)
  have hx := coeffMap_generator ι f g pf pg hf hg hg0
  have key := hE1' _ k f g Φ Ψ 1 1 one_ne_zero one_ne_zero
    (by rw [Int.cast_one, one_smul]; exact hΦ) (by rw [Int.cast_one, one_smul]; exact hΨ) hqg hx
  refine ⟨Φ, Ψ, hΦ, hΨ, hΨne, ?_⟩
  rw [key]
  simp [qC]

end TauSymm

def dPrime (p M : ℕ) (y w₀ : ℤ) : ℕ := ZMod.val ((((p : ℤ) ^ 2 * w₀ - (M : ℤ) * y : ℤ)) : ZMod (M * p))

end LEGS
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_coprime_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_of_atkinLehnerSlash_p_of_atkinLehnerSlash_sq.LEGS"

theorem LEGS.coeffMap_injective_of_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (ModularCurve.coeffMap f) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries S => s.coeff n) h
  simp only [ModularCurve.coeffMap_coeff] at h1
  exact hf h1

theorem LEGS.dPrime_coprime (p M : ℕ) (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1) [NeZero (M * p)] :
    (LEGS.dPrime p M y w₀).Coprime (M * p) := by
  have hu : IsCoprime (((M * p : ℕ)) : ℤ) ((p : ℤ) ^ 2 * w₀ - (M : ℤ) * y) := by
    rw [Nat.cast_mul]
    apply IsCoprime.mul_left
    · exact ⟨-(2 * y + (M : ℤ) * y ^ 2 - y * w₀), w₀, by linear_combination ((p : ℤ) * w₀ + 1 + (M : ℤ) * y) * hrel⟩
    · exact ⟨w₀ - (p : ℤ) * w₀, 1, by linear_combination hrel⟩
  have hunit : IsUnit ((((p : ℤ) ^ 2 * w₀ - (M : ℤ) * y : ℤ)) : ZMod (M * p)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime _ (M * p)).mpr hu
  rw [LEGS.dPrime, ← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
  exact hunit

namespace LEGS

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

section Spec

theorem leg1_gen
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) [NeZero p]
    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p)
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
    (γ' : SL(2, ℤ)) (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w₀, -y; -(M : ℤ), (p : ℤ)])
    (y₂ w₂ : ℤ) (hrel₂ : (p : ℤ) ^ 2 * w₂ - (M : ℤ) * y₂ = 1)
    (δ δ' : SL(2, ℤ)) (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y₂; (M : ℤ), (p : ℤ) ^ 2 * w₂])
    (τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hE1' : (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ.symm x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)))
    (W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))))
    (hWE0 : (∀ x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))), ∃ (k : ℤ) (f g : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 ∧
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∧
        (∃ (φ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D : ℤ), D ≠ 0 ∧ (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E : ℤ), E ≠ 0 ∧ (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (φ' : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D' : ℤ), D' ≠ 0 ∧ (⇑φ' : UpperHalfPlane → ℂ) = (D' : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (ψ' : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E' : ℤ), E' ≠ 0 ∧ (⇑ψ' : UpperHalfPlane → ℂ) = (E' : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)))))
    (hWE1 : (∀ (x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) (k : ℤ) (f g φ ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((W x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)))
    {k : ℤ} (f g : ModularForm (Γb (M * p)) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    coeffMap ι ((W (heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p (τ.symm (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(x1FunctionFieldBar (M * p))))) :
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffMap ι ((heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p (diamondAutBar (M * p) 1 (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(x1FunctionFieldBar (M * p)))) :
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hγ'0 : γ' ∈ Gamma0 M := by
    rw [Gamma0_mem, show (γ' 1 0 : ℤ) = -(M : ℤ) by rw [hγ']; rfl]
    simp
  have hγ'p : (p : ℤ) ∣ γ' 1 1 := by
    rw [show (γ' 1 1 : ℤ) = (p : ℤ) by rw [hγ']; rfl]

  obtain ⟨Φ, Ψ, hΦ, hΨ, hΨ0, hτs⟩ := tau_symm_generator p M hpM ι γ' hγ'0 hγ'p τ hE1' f g pf pg hf hg hg0

  have hu : coeffMap ι ((heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p (τ.symm (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(x1FunctionFieldBar (M * p)))) :
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
      qC (⇑Φ) / qC (⇑Ψ) := by
    rw [coe_heckeAlphaOneBar]; exact hτs
  obtain ⟨k'', f'', g'', hg'', hu', ⟨φ₂, D₂, hD₂, hφ₂⟩, ⟨ψ₂, E₂, hE₂, hψ₂⟩, -, -⟩ :=
    hWE0 (heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p (τ.symm (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(x1FunctionFieldBar (M * p)))))
  have hWu := hWE1 _ k'' f'' g'' φ₂ ψ₂ D₂ E₂ hD₂ hE₂ hφ₂ hψ₂ hg'' hu'
  rw [hWu]

  have hS₁ : S₁ (p := p) y w₀ y₂ w₂ ∈ Gamma1 (M * p) := by
    rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [S₁]
  have slashS₁ : ∀ F : ModularForm (Γb (M * p)) k, (⇑F) ∣[k] S₁ (p := p) y w₀ y₂ w₂ = ⇑F := fun F => by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hS₁)
  have hqg : qC (⇑g) ≠ 0 := by
    rw [← ιC_intSeriesC hg]; exact (map_ne_zero_iff _ ιC_injective).mpr hg0
  have hratio := ratio_law_of_presentations (N := M * p) (p := p) (restrictForm Γt_le_Γb Φ) (restrictForm Γt_le_Γb Ψ)
    f'' g'' φ₂ ψ₂ D₂ E₂ hD₂ hE₂ δ hφ₂ hψ₂ hΨ0 hg'' (hu.symm.trans hu')
    (levelRaise (ℓ := p) f) (levelRaise (ℓ := p) g) (((p : ℂ) ^ k)⁻¹) (inv_ne_zero (zpow_ne_zero _ hpC))
    (fun z => by
      rw [coe_restrictForm, hΦ, AL₁ y w₀ y₂ w₂ hrel hrel₂ γ' δ hγ' hδ k (⇑f) z, slashS₁ f, levelRaise_apply])
    (fun z => by
      rw [coe_restrictForm, hΨ, AL₁ y w₀ y₂ w₂ hrel hrel₂ γ' δ hγ' hδ k (⇑g) z, slashS₁ g, levelRaise_apply])
    (by rw [qC_levelRaise]; exact (map_ne_zero_iff _ (qExpand_injective p)).mpr hqg)
  rw [show HahnSeries.C ((E₂ : ℂ) / (D₂ : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ₂) /
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ₂) = _ from hratio, qC_levelRaise, qC_levelRaise, ← map_div₀]

  rw [coe_heckeBetaOneBar (M * p) p hβdef, coeffMap_qExpand]
  congr 1
  have hD := coeffMap_diamondAutBar_mul_qC (M * p) ι (d := 1) (Nat.coprime_one_left _) f g pf pg hf hg hg0 1
    (Subgroup.one_mem _) (by simp)
  rw [SlashAction.slash_one, SlashAction.slash_one] at hD
  exact ((eq_div_iff hqg).mpr hD).symm

theorem leg2_gen
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) [NeZero p]
    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p)
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
    (γ' : SL(2, ℤ)) (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w₀, -y; -(M : ℤ), (p : ℤ)])
    (y₂ w₂ : ℤ) (hrel₂ : (p : ℤ) ^ 2 * w₂ - (M : ℤ) * y₂ = 1)
    (δ δ' : SL(2, ℤ)) (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y₂; (M : ℤ), (p : ℤ) ^ 2 * w₂])
    (τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hE1' : (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ.symm x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)))
    (W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))))
    (hWE0 : (∀ x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))), ∃ (k : ℤ) (f g : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 ∧
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∧
        (∃ (φ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D : ℤ), D ≠ 0 ∧ (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E : ℤ), E ≠ 0 ∧ (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (φ' : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D' : ℤ), D' ≠ 0 ∧ (⇑φ' : UpperHalfPlane → ℂ) = (D' : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (ψ' : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E' : ℤ), E' ≠ 0 ∧ (⇑ψ' : UpperHalfPlane → ℂ) = (E' : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)))))
    (hWE1 : (∀ (x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) (k : ℤ) (f g φ ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((W x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)))
    {k : ℤ} (f g : ModularForm (Γb (M * p)) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    coeffMap ι ((W (heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p (τ.symm (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(x1FunctionFieldBar (M * p))))) :
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffMap ι ((heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p (diamondAutBar (M * p) (dPrime p M y w₀) (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(x1FunctionFieldBar (M * p)))) :
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp⟩
  have hγ'0 : γ' ∈ Gamma0 M := by
    rw [Gamma0_mem, show (γ' 1 0 : ℤ) = -(M : ℤ) by rw [hγ']; rfl]
    simp
  have hγ'p : (p : ℤ) ∣ γ' 1 1 := by
    rw [show (γ' 1 1 : ℤ) = (p : ℤ) by rw [hγ']; rfl]
  obtain ⟨Φ, Ψ, hΦ, hΨ, hΨ0, hτs⟩ := tau_symm_generator p M hpM ι γ' hγ'0 hγ'p τ hE1' f g pf pg hf hg hg0

  have hv : coeffMap ι ((heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p (τ.symm (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(x1FunctionFieldBar (M * p)))) :
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
      qC (⇑(levelRaise (ℓ := p) Φ)) / qC (⇑(levelRaise (ℓ := p) Ψ)) := by
    rw [coe_heckeBetaOneBar (M * p) p hβdef, coeffMap_qExpand, hτs, map_div₀, qC_levelRaise, qC_levelRaise]
  obtain ⟨k'', f'', g'', hg'', hv', ⟨φ₂, D₂, hD₂, hφ₂⟩, ⟨ψ₂, E₂, hE₂, hψ₂⟩, -, -⟩ :=
    hWE0 (heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p (τ.symm (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          ↥(x1FunctionFieldBar (M * p)))))
  have hWv := hWE1 _ k'' f'' g'' φ₂ ψ₂ D₂ E₂ hD₂ hE₂ hφ₂ hψ₂ hg'' hv'
  rw [hWv]

  have hS₂ : S₂ (p := p) y w₀ y₂ w₂ hrel hrel₂ ∈ Gamma0 (M * p) := by
    rw [Gamma0_mem, show ((S₂ (p := p) y w₀ y₂ w₂ hrel hrel₂) 1 0 : ℤ) = (M : ℤ) * p * (1 - p) from rfl,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨1 - p, by push_cast; ring⟩
  have hS₂00 : (((S₂ (p := p) y w₀ y₂ w₂ hrel hrel₂) 0 0 : ℤ) : ZMod (M * p)) = ((dPrime p M y w₀ : ℕ) : ZMod (M * p)) := by
    rw [dPrime, ZMod.natCast_zmod_val]; rfl
  have hqg : qC (⇑g) ≠ 0 := by
    rw [← ιC_intSeriesC hg]; exact (map_ne_zero_iff _ ιC_injective).mpr hg0
  have hΨL0 : qC (⇑(levelRaise (ℓ := p) Ψ)) ≠ 0 := by
    rw [qC_levelRaise]; exact (map_ne_zero_iff _ (qExpand_injective p)).mpr hΨ0
  have hgS : qC (⇑(diaForm (S₂ (p := p) y w₀ y₂ w₂ hrel hrel₂) hS₂ g)) ≠ 0 := qC_diaForm_ne_zero hg hg0 _ hS₂
  have hratio := ratio_law_of_presentations (N := M * p) (p := p) (levelRaise (ℓ := p) Φ) (levelRaise (ℓ := p) Ψ)
    f'' g'' φ₂ ψ₂ D₂ E₂ hD₂ hE₂ δ hφ₂ hψ₂ hΨL0 hg'' (hv.symm.trans hv')
    (restrictForm Γt_le_Γb (diaForm (S₂ (p := p) y w₀ y₂ w₂ hrel hrel₂) hS₂ f))
    (restrictForm Γt_le_Γb (diaForm (S₂ (p := p) y w₀ y₂ w₂ hrel hrel₂) hS₂ g))
    (((p : ℂ) ^ (2 * k))⁻¹) (inv_ne_zero (zpow_ne_zero _ hpC))
    (fun z => by
      rw [coe_levelRaise, hΦ, AL₂ y w₀ y₂ w₂ hrel hrel₂ γ' δ hγ' hδ k (⇑f) z, coe_restrictForm, coe_diaForm])
    (fun z => by
      rw [coe_levelRaise, hΨ, AL₂ y w₀ y₂ w₂ hrel hrel₂ γ' δ hγ' hδ k (⇑g) z, coe_restrictForm, coe_diaForm])
    hgS
  rw [show HahnSeries.C ((E₂ : ℂ) / (D₂ : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ₂) /
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ₂) = _ from hratio]

  rw [coe_heckeAlphaOneBar]
  have hD := coeffMap_diamondAutBar_mul_qC (M * p) ι (d := dPrime p M y w₀) (LEGS.dPrime_coprime p M y w₀ hrel) f g pf pg hf hg hg0
    (S₂ (p := p) y w₀ y₂ w₂ hrel hrel₂) hS₂ hS₂00
  rw [coe_restrictForm, coe_restrictForm, coe_diaForm, coe_diaForm]
  rw [coe_diaForm] at hgS
  exact ((eq_div_iff hgS).mpr hD).symm

end Spec
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_coprime_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_of_atkinLehnerSlash_p_of_atkinLehnerSlash_sq.LEGS"

end LEGS
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_coprime_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_of_atkinLehnerSlash_p_of_atkinLehnerSlash_sq.LEGS"

open ModularCurve LEGS in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) (hM : 5 ≤ M)
    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p)
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
    (γ γ' : SL(2, ℤ)) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) * w₀])
    (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w₀, -y; -(M : ℤ), (p : ℤ)])
    (y₂ w₂ : ℤ) (hrel₂ : (p : ℤ) ^ 2 * w₂ - (M : ℤ) * y₂ = 1)
    (δ δ' : SL(2, ℤ)) (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y₂; (M : ℤ), (p : ℤ) ^ 2 * w₂])
    (hδ' : (δ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w₂, -y₂; -(M : ℤ), (p : ℤ) ^ 2])
    (τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hτ :

      (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ∃ (k : ℤ) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 ∧
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∧
        (∃ (φ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D : ℤ), D ≠ 0 ∧ (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z))) ∧
        (∃ (ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (E : ℤ), E ≠ 0 ∧ (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z))) ∧
        (∃ (φ' : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D' : ℤ), D' ≠ 0 ∧ (⇑φ' : UpperHalfPlane → ℂ) = (D' : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z))) ∧
        (∃ (ψ' : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (E' : ℤ), E' ≠ 0 ∧ (⇑ψ' : UpperHalfPlane → ℂ) = (E' : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)))) ∧

      (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ.symm x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ j : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ((j : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq →
        ((τ j : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ p ModularCurve.jq)))
    (W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))))
    (hW :

      (∀ x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))), ∃ (k : ℤ) (f g : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 ∧
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∧
        (∃ (φ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D : ℤ), D ≠ 0 ∧ (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E : ℤ), E ≠ 0 ∧ (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (φ' : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D' : ℤ), D' ≠ 0 ∧ (⇑φ' : UpperHalfPlane → ℂ) = (D' : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (ψ' : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E' : ℤ), E' ≠ 0 ∧ (⇑ψ' : UpperHalfPlane → ℂ) = (E' : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)))) ∧

      (∀ (x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) (k : ℤ) (f g φ ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((W x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ (x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) (k : ℤ) (f g φ ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((W.symm x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))), ((j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq →
        ((W j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ (p ^ 2) ModularCurve.jq))) :
    ∃ d d' : ℕ, d.Coprime (M * p) ∧ d'.Coprime (M * p) ∧

        (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)),
          W (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p x) =
            ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p
              (ModularCurve.diamondAutBar (M * p) d (τ x))) ∧

        (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)),
          W (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p x) =
            ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p
              (ModularCurve.diamondAutBar (M * p) d' (τ x))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨hτE0, hτE1, hτE1', hτE2⟩ := hτ
  obtain ⟨hWE0, hWE1, hWE1', hWE2⟩ := hW
  have hιinj : Function.Injective (ModularCurve.coeffMap ι) := LEGS.coeffMap_injective_of_injective ι.injective

  have H1 : W.toAlgHom.comp ((heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p).comp τ.symm.toAlgHom) =
      (heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p).comp (diamondAutBar (M * p) 1).toAlgHom := by
    refine IntermediateField.algHom_ext_of_eq_adjoin (F := AlgebraicClosure ℚ)
      (S := x1FunctionFieldBar (M * p)) (s := ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (x1FunctionField (M * p) : Set (LaurentSeries ℚ)))
      rfl fun x hx => ?_
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := LEGS.mem_Sb_of_mem hz
    apply Subtype.ext
    apply hιinj
    exact LEGS.leg1_gen p M hpM hβdef ι y w₀ hrel γ' hγ' y₂ w₂ hrel₂ δ δ' hδ τ hτE1' W hWE0 hWE1 f g pf pg hf hg hg0

  have H2 : W.toAlgHom.comp ((heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p).comp τ.symm.toAlgHom) =
      (heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p).comp (diamondAutBar (M * p) (LEGS.dPrime p M y w₀)).toAlgHom := by
    refine IntermediateField.algHom_ext_of_eq_adjoin (F := AlgebraicClosure ℚ)
      (S := x1FunctionFieldBar (M * p)) (s := ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (x1FunctionField (M * p) : Set (LaurentSeries ℚ)))
      rfl fun x hx => ?_
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := LEGS.mem_Sb_of_mem hz
    apply Subtype.ext
    apply hιinj
    exact LEGS.leg2_gen p M hpM hβdef ι y w₀ hrel γ' hγ' y₂ w₂ hrel₂ δ δ' hδ τ hτE1' W hWE0 hWE1 f g pf pg hf hg hg0
  refine ⟨1, LEGS.dPrime p M y w₀, Nat.coprime_one_left _, LEGS.dPrime_coprime p M y w₀ hrel, fun x => ?_, fun x => ?_⟩
  · have h := congrArg (fun φ : ↥(x1FunctionFieldBar (M * p)) →ₐ[AlgebraicClosure ℚ]
        ↥(laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ (M * p) (M * p * p))) => φ (τ x)) H1
    simpa using h
  · have h := congrArg (fun φ : ↥(x1FunctionFieldBar (M * p)) →ₐ[AlgebraicClosure ℚ]
        ↥(laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ (M * p) (M * p * p))) => φ (τ x)) H2
    simpa using h

end
end S_ModularCurve_XOneP_exists_coprime_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_of_atkinLehnerSlash_p_of_atkinLehnerSlash_sq
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_coprime_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_of_atkinLehnerSlash_p_of_atkinLehnerSlash_sq (solution)
