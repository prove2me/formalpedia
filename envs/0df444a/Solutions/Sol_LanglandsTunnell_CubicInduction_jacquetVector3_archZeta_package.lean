-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/48bcf5e0-277d-5e5e-a1a1-f031bcd7ff87

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Data.Real.Sign
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetIntegrand3_integrable_and_jacquetVector3_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove
import Theorems.Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_jacquetVector3
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_scalar_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR
import Theorems.Thm_LanglandsTunnell_CubicInduction_heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR
import Theorems.Thm_LanglandsTunnell_CubicInduction_archZeta30_jacquetVector3_eq_archFactor_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_archZetaDual31_jacquetVector3_mul_archFactor_eq
import Theorems.Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
import Theorems.Thm_LanglandsTunnell_CubicInduction_isKFinite_jacquetVector3
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZeta30_jacquetVector3_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Ring.Units
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_archZeta_package
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_archZeta_package.LanglandsTunnell.CubicLambda"

p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_archZeta_package.LanglandsTunnell"

namespace GammaRatioStrip

private def StirlingInput : Prop :=
  ∀ σ₁ σ₂ : ℝ, ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → 1 ≤ |w.im| →
    ‖Complex.Gamma w‖ ≤ A * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|) ∧
      Real.exp (-(Real.pi / 2) * |w.im|) ≤ A * (1 + |w.im|) ^ N * ‖Complex.Gamma w‖

private def UpperRate (σ₁ σ₂ : ℝ) (F : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∃ (B T₀ : ℝ) (N : ℕ), 0 ≤ B ∧ 1 ≤ T₀ ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
    ‖F s‖ ≤ B * |s.im| ^ N * Real.exp (-ρ * |s.im|)

private def LowerRate (σ₁ σ₂ : ℝ) (F : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∃ (B T₀ : ℝ) (N : ℕ), 0 ≤ B ∧ 1 ≤ T₀ ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
    Real.exp (-ρ * |s.im|) ≤ B * |s.im| ^ N * ‖F s‖

private theorem upperRate_one (σ₁ σ₂ : ℝ) : UpperRate σ₁ σ₂ (fun _ => 1) 0 :=
  ⟨1, 1, 0, zero_le_one, le_rfl, fun s _ _ _ => by simp⟩

private theorem lowerRate_one (σ₁ σ₂ : ℝ) : LowerRate σ₁ σ₂ (fun _ => 1) 0 :=
  ⟨1, 1, 0, zero_le_one, le_rfl, fun s _ _ _ => by simp⟩

private theorem UpperRate.mul {σ₁ σ₂ : ℝ} {F G : ℂ → ℂ} {ρ₁ ρ₂ : ℝ} (hF : UpperRate σ₁ σ₂ F ρ₁)
    (hG : UpperRate σ₁ σ₂ G ρ₂) : UpperRate σ₁ σ₂ (fun s => F s * G s) (ρ₁ + ρ₂) := by
  obtain ⟨B₁, T₁, N₁, hB₁, hT₁, h₁⟩ := hF
  obtain ⟨B₂, T₂, N₂, hB₂, hT₂, h₂⟩ := hG
  refine ⟨B₁ * B₂, max T₁ T₂, N₁ + N₂, mul_nonneg hB₁ hB₂, le_trans hT₁ (le_max_left _ _),
    fun s hs₁ hs₂ hs => ?_⟩
  have e₁ := h₁ s hs₁ hs₂ (le_trans (le_max_left _ _) hs)
  have e₂ := h₂ s hs₁ hs₂ (le_trans (le_max_right _ _) hs)
  calc ‖F s * G s‖ = ‖F s‖ * ‖G s‖ := norm_mul _ _
    _ ≤ (B₁ * |s.im| ^ N₁ * Real.exp (-ρ₁ * |s.im|)) * (B₂ * |s.im| ^ N₂ * Real.exp (-ρ₂ * |s.im|)) :=
        mul_le_mul e₁ e₂ (norm_nonneg _) (by positivity)
    _ = B₁ * B₂ * |s.im| ^ (N₁ + N₂) * Real.exp (-(ρ₁ + ρ₂) * |s.im|) := by
        rw [pow_add, show -(ρ₁ + ρ₂) * |s.im| = -ρ₁ * |s.im| + -ρ₂ * |s.im| by ring, Real.exp_add]
        ring

private theorem LowerRate.mul {σ₁ σ₂ : ℝ} {F G : ℂ → ℂ} {ρ₁ ρ₂ : ℝ} (hF : LowerRate σ₁ σ₂ F ρ₁)
    (hG : LowerRate σ₁ σ₂ G ρ₂) : LowerRate σ₁ σ₂ (fun s => F s * G s) (ρ₁ + ρ₂) := by
  obtain ⟨B₁, T₁, N₁, hB₁, hT₁, h₁⟩ := hF
  obtain ⟨B₂, T₂, N₂, hB₂, hT₂, h₂⟩ := hG
  refine ⟨B₁ * B₂, max T₁ T₂, N₁ + N₂, mul_nonneg hB₁ hB₂, le_trans hT₁ (le_max_left _ _),
    fun s hs₁ hs₂ hs => ?_⟩
  have e₁ := h₁ s hs₁ hs₂ (le_trans (le_max_left _ _) hs)
  have e₂ := h₂ s hs₁ hs₂ (le_trans (le_max_right _ _) hs)
  calc Real.exp (-(ρ₁ + ρ₂) * |s.im|) = Real.exp (-ρ₁ * |s.im|) * Real.exp (-ρ₂ * |s.im|) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ (B₁ * |s.im| ^ N₁ * ‖F s‖) * (B₂ * |s.im| ^ N₂ * ‖G s‖) :=
        mul_le_mul e₁ e₂ (Real.exp_pos _).le (by positivity)
    _ = B₁ * B₂ * |s.im| ^ (N₁ + N₂) * ‖F s * G s‖ := by
        rw [norm_mul, pow_add]
        ring

private theorem UpperRate.mono_rate {σ₁ σ₂ : ℝ} {F : ℂ → ℂ} {ρ ρ' : ℝ} (h : UpperRate σ₁ σ₂ F ρ) (hρ : ρ' ≤ ρ) :
    UpperRate σ₁ σ₂ F ρ' := by
  obtain ⟨B, T₀, N, hB, hT, hF⟩ := h
  refine ⟨B, T₀, N, hB, hT, fun s hs₁ hs₂ hs => (hF s hs₁ hs₂ hs).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hρ) (abs_nonneg _))) (by positivity)

private theorem LowerRate.mono_rate {σ₁ σ₂ : ℝ} {F : ℂ → ℂ} {ρ ρ' : ℝ} (h : LowerRate σ₁ σ₂ F ρ) (hρ : ρ ≤ ρ') :
    LowerRate σ₁ σ₂ F ρ' := by
  obtain ⟨B, T₀, N, hB, hT, hF⟩ := h
  refine ⟨B, T₀, N, hB, hT, fun s hs₁ hs₂ hs => le_trans ?_ (hF s hs₁ hs₂ hs)⟩
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hρ) (abs_nonneg _))

private theorem upperRate_multiset_prod {σ₁ σ₂ ρ : ℝ} (f : ℂ → ℂ → ℂ) (m : Multiset ℂ)
    (hf : ∀ μ ∈ m, UpperRate σ₁ σ₂ (f μ) ρ) :
    UpperRate σ₁ σ₂ (fun s => (m.map fun μ => f μ s).prod) (ρ * Multiset.card m) := by
  induction m using Multiset.induction_on with
  | empty => simpa using upperRate_one σ₁ σ₂
  | cons a m ih =>
    have ha : UpperRate σ₁ σ₂ (f a) ρ := hf a (Multiset.mem_cons_self a m)
    have hm := ih fun μ hμ => hf μ (Multiset.mem_cons_of_mem hμ)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    exact (ha.mul hm).mono_rate (le_of_eq (by push_cast; ring))

private theorem lowerRate_multiset_prod {σ₁ σ₂ ρ : ℝ} (f : ℂ → ℂ → ℂ) (m : Multiset ℂ)
    (hf : ∀ μ ∈ m, LowerRate σ₁ σ₂ (f μ) ρ) :
    LowerRate σ₁ σ₂ (fun s => (m.map fun μ => f μ s).prod) (ρ * Multiset.card m) := by
  induction m using Multiset.induction_on with
  | empty => simpa using lowerRate_one σ₁ σ₂
  | cons a m ih =>
    have ha : LowerRate σ₁ σ₂ (f a) ρ := hf a (Multiset.mem_cons_self a m)
    have hm := ih fun μ hμ => hf μ (Multiset.mem_cons_of_mem hμ)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    exact (ha.mul hm).mono_rate (le_of_eq (by push_cast; ring))

private def ZUpper (g : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∀ a₁ a₂ : ℝ, ∃ (B : ℝ) (N : ℕ), 0 ≤ B ∧ ∀ z : ℂ, a₁ ≤ z.re → z.re ≤ a₂ → 2 ≤ |z.im| →
    ‖g z‖ ≤ B * (1 + |z.im|) ^ N * Real.exp (-ρ * |z.im|)

private def ZLower (g : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∀ a₁ a₂ : ℝ, ∃ (B : ℝ) (N : ℕ), 0 ≤ B ∧ ∀ z : ℂ, a₁ ≤ z.re → z.re ≤ a₂ → 2 ≤ |z.im| →
    Real.exp (-ρ * |z.im|) ≤ B * (1 + |z.im|) ^ N * ‖g z‖

private theorem one_le_pi : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]

private theorem one_le_two_pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]

private theorem norm_Gammaℝ (z : ℂ) : ‖Complex.Gammaℝ z‖ = Real.pi ^ (-z.re / 2) * ‖Complex.Gamma (z / 2)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.div_ofNat_re,
    Complex.neg_re]

private theorem norm_Gammaℂ (z : ℂ) :
    ‖Complex.Gammaℂ z‖ = ‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-z.re) * ‖Complex.Gamma z‖ := by
  have hb : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.Gammaℂ_def, norm_mul, norm_mul, hb, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]

private theorem half_im_facts {z : ℂ} (h : 2 ≤ |z.im|) : |(z / 2).im| = |z.im| / 2 ∧ 1 ≤ |(z / 2).im| := by
  rw [Complex.div_ofNat_im, abs_div, abs_two]
  exact ⟨rfl, by linarith⟩

private theorem exp_half (x : ℝ) : Real.exp (-(Real.pi / 2) * (x / 2)) = Real.exp (-(Real.pi / 4) * x) := by
  congr 1
  ring

private theorem pow_half_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) : (1 + x / 2) ^ N ≤ (1 + x) ^ N := by
  have h : 1 + x / 2 ≤ 1 + x := by linarith
  exact pow_le_pow_left₀ (by linarith) h N

private theorem zUpper_Gammaℝ (hS : StirlingInput) : ZUpper Complex.Gammaℝ (Real.pi / 4) := by
  intro a₁ a₂
  obtain ⟨A, N, hA⟩ := hS (a₁ / 2) (a₂ / 2)
  refine ⟨Real.pi ^ (-a₁ / 2) * |A|, N, by positivity, fun z hz₁ hz₂ hz => ?_⟩
  obtain ⟨him, him1⟩ := half_im_facts hz
  have hre : (z / 2).re = z.re / 2 := Complex.div_ofNat_re z 2
  have hΓ := (hA (z / 2) (by rw [hre]; linarith) (by rw [hre]; linarith) him1).1
  rw [him, exp_half] at hΓ
  have hπ : Real.pi ^ (-z.re / 2) ≤ Real.pi ^ (-a₁ / 2) :=
    Real.rpow_le_rpow_of_exponent_le one_le_pi (by linarith)
  have hΓ' : ‖Complex.Gamma (z / 2)‖ ≤ |A| * (1 + |z.im|) ^ N * Real.exp (-(Real.pi / 4) * |z.im|) := by
    refine hΓ.trans ?_
    have h1 : A * (1 + |z.im| / 2) ^ N ≤ |A| * (1 + |z.im|) ^ N :=
      mul_le_mul (le_abs_self A) (pow_half_le (abs_nonneg _) N) (by positivity) (abs_nonneg A)
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  calc ‖Complex.Gammaℝ z‖ = Real.pi ^ (-z.re / 2) * ‖Complex.Gamma (z / 2)‖ := norm_Gammaℝ z
    _ ≤ Real.pi ^ (-a₁ / 2) * (|A| * (1 + |z.im|) ^ N * Real.exp (-(Real.pi / 4) * |z.im|)) :=
        mul_le_mul hπ hΓ' (norm_nonneg _) (by positivity)
    _ = Real.pi ^ (-a₁ / 2) * |A| * (1 + |z.im|) ^ N * Real.exp (-(Real.pi / 4) * |z.im|) := by ring

private theorem zLower_Gammaℝ (hS : StirlingInput) : ZLower Complex.Gammaℝ (Real.pi / 4) := by
  intro a₁ a₂
  obtain ⟨A, N, hA⟩ := hS (a₁ / 2) (a₂ / 2)
  have hPlow : 0 < Real.pi ^ (-a₂ / 2) := by positivity
  refine ⟨|A| * (Real.pi ^ (-a₂ / 2))⁻¹, N, by positivity, fun z hz₁ hz₂ hz => ?_⟩
  obtain ⟨him, him1⟩ := half_im_facts hz
  have hre : (z / 2).re = z.re / 2 := Complex.div_ofNat_re z 2
  have hΓ := (hA (z / 2) (by rw [hre]; linarith) (by rw [hre]; linarith) him1).2
  rw [him, exp_half] at hΓ
  have hπ : Real.pi ^ (-a₂ / 2) ≤ Real.pi ^ (-z.re / 2) :=
    Real.rpow_le_rpow_of_exponent_le one_le_pi (by linarith)
  have hPG : Real.pi ^ (-a₂ / 2) * ‖Complex.Gamma (z / 2)‖ ≤ ‖Complex.Gammaℝ z‖ := by
    rw [norm_Gammaℝ]
    exact mul_le_mul_of_nonneg_right hπ (norm_nonneg _)
  have hG : ‖Complex.Gamma (z / 2)‖ ≤ (Real.pi ^ (-a₂ / 2))⁻¹ * ‖Complex.Gammaℝ z‖ := by
    calc ‖Complex.Gamma (z / 2)‖
        = (Real.pi ^ (-a₂ / 2))⁻¹ * (Real.pi ^ (-a₂ / 2) * ‖Complex.Gamma (z / 2)‖) :=
          (inv_mul_cancel_left₀ hPlow.ne' _).symm
      _ ≤ (Real.pi ^ (-a₂ / 2))⁻¹ * ‖Complex.Gammaℝ z‖ := mul_le_mul_of_nonneg_left hPG (by positivity)
  calc Real.exp (-(Real.pi / 4) * |z.im|) ≤ A * (1 + |z.im| / 2) ^ N * ‖Complex.Gamma (z / 2)‖ := hΓ
    _ ≤ |A| * (1 + |z.im|) ^ N * ((Real.pi ^ (-a₂ / 2))⁻¹ * ‖Complex.Gammaℝ z‖) := by
        refine mul_le_mul ?_ hG (norm_nonneg _) (by positivity)
        exact mul_le_mul (le_abs_self A) (pow_half_le (abs_nonneg _) N) (by positivity) (abs_nonneg A)
    _ = |A| * (Real.pi ^ (-a₂ / 2))⁻¹ * (1 + |z.im|) ^ N * ‖Complex.Gammaℝ z‖ := by ring

private theorem zUpper_Gammaℂ (hS : StirlingInput) : ZUpper Complex.Gammaℂ (Real.pi / 2) := by
  intro a₁ a₂
  obtain ⟨A, N, hA⟩ := hS a₁ a₂
  refine ⟨‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₁) * |A|, N, by positivity, fun z hz₁ hz₂ hz => ?_⟩
  have hΓ := (hA z hz₁ hz₂ (by linarith)).1
  have hπ : (2 * Real.pi) ^ (-z.re) ≤ (2 * Real.pi) ^ (-a₁) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two_pi (by linarith)
  have hΓ' : ‖Complex.Gamma z‖ ≤ |A| * (1 + |z.im|) ^ N * Real.exp (-(Real.pi / 2) * |z.im|) :=
    hΓ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
      (Real.exp_pos _).le)
  calc ‖Complex.Gammaℂ z‖ = ‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-z.re) * ‖Complex.Gamma z‖ := norm_Gammaℂ z
    _ ≤ ‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₁) *
          (|A| * (1 + |z.im|) ^ N * Real.exp (-(Real.pi / 2) * |z.im|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hπ (norm_nonneg _)) hΓ' (norm_nonneg _) (by positivity)
    _ = ‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₁) * |A| * (1 + |z.im|) ^ N * Real.exp (-(Real.pi / 2) * |z.im|) := by
        ring

private theorem zLower_Gammaℂ (hS : StirlingInput) : ZLower Complex.Gammaℂ (Real.pi / 2) := by
  intro a₁ a₂
  obtain ⟨A, N, hA⟩ := hS a₁ a₂
  have h2 : 0 < ‖(2 : ℂ)‖ := norm_pos_iff.2 two_ne_zero
  have hPlow : 0 < ‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₂) := by positivity
  refine ⟨|A| * (‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₂))⁻¹, N, by positivity, fun z hz₁ hz₂ hz => ?_⟩
  have hΓ := (hA z hz₁ hz₂ (by linarith)).2
  have hπ : (2 * Real.pi) ^ (-a₂) ≤ (2 * Real.pi) ^ (-z.re) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two_pi (by linarith)
  have hPG : ‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₂) * ‖Complex.Gamma z‖ ≤ ‖Complex.Gammaℂ z‖ := by
    rw [norm_Gammaℂ]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hπ (norm_nonneg _)) (norm_nonneg _)
  have hG : ‖Complex.Gamma z‖ ≤ (‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₂))⁻¹ * ‖Complex.Gammaℂ z‖ := by
    calc ‖Complex.Gamma z‖
        = (‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₂))⁻¹ * (‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₂) * ‖Complex.Gamma z‖) :=
          (inv_mul_cancel_left₀ hPlow.ne' _).symm
      _ ≤ (‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₂))⁻¹ * ‖Complex.Gammaℂ z‖ := mul_le_mul_of_nonneg_left hPG (by positivity)
  calc Real.exp (-(Real.pi / 2) * |z.im|) ≤ A * (1 + |z.im|) ^ N * ‖Complex.Gamma z‖ := hΓ
    _ ≤ |A| * (1 + |z.im|) ^ N * ((‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₂))⁻¹ * ‖Complex.Gammaℂ z‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)) hG (norm_nonneg _)
          (by positivity)
    _ = |A| * (‖(2 : ℂ)‖ * (2 * Real.pi) ^ (-a₂))⁻¹ * (1 + |z.im|) ^ N * ‖Complex.Gammaℂ z‖ := by ring

private theorem abs_shift_facts (t c : ℝ) : |t| - |c| ≤ |t + c| ∧ |t + c| ≤ |t| + |c| := by
  obtain ⟨h₁, h₂⟩ := abs_le.1 (le_refl |t + c|)
  obtain ⟨h₃, h₄⟩ := abs_le.1 (le_refl |c|)
  obtain ⟨h₅, h₆⟩ := abs_le.1 (le_refl |t|)
  constructor
  · have : |t| ≤ |t + c| + |c| := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  · exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem one_add_abs_shift_le {t c x : ℝ} (ht : 1 ≤ |t|) (hx : |x| ≤ |t| + |c|) :
    1 + |x| ≤ (2 + |c|) * |t| := by
  have hc := abs_nonneg c
  nlinarith

private theorem upperRate_of_zUpper {g : ℂ → ℂ} {ρ : ℝ} (hg : ZUpper g ρ) (hρ : 0 ≤ ρ) (σ₁ σ₂ : ℝ) (μ : ℂ) :
    UpperRate σ₁ σ₂ (fun s => g (s + μ)) ρ := by
  obtain ⟨B, N, hB, h⟩ := hg (σ₁ + μ.re) (σ₂ + μ.re)
  refine ⟨B * (2 + |μ.im|) ^ N * Real.exp (ρ * |μ.im|), 2 + |μ.im|, N, by positivity,
    by linarith [abs_nonneg μ.im], fun s hs₁ hs₂ hs => ?_⟩
  have hre : (s + μ).re = s.re + μ.re := Complex.add_re s μ
  have him : (s + μ).im = s.im + μ.im := Complex.add_im s μ
  obtain ⟨hlo, hhi⟩ := abs_shift_facts s.im μ.im
  rw [← him] at hlo hhi
  have ht : 1 ≤ |s.im| := by linarith [abs_nonneg μ.im]
  have hz := h (s + μ) (by rw [hre]; linarith) (by rw [hre]; linarith) (by linarith)
  have hpow : (1 + |(s + μ).im|) ^ N ≤ (2 + |μ.im|) ^ N * |s.im| ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_abs_shift_le ht hhi) N
  have hexp : Real.exp (-ρ * |(s + μ).im|) ≤ Real.exp (ρ * |μ.im|) * Real.exp (-ρ * |s.im|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hlo hρ
    linarith
  calc ‖g (s + μ)‖ ≤ B * (1 + |(s + μ).im|) ^ N * Real.exp (-ρ * |(s + μ).im|) := hz
    _ ≤ B * ((2 + |μ.im|) ^ N * |s.im| ^ N) * (Real.exp (ρ * |μ.im|) * Real.exp (-ρ * |s.im|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hB) hexp (Real.exp_pos _).le (by positivity)
    _ = B * (2 + |μ.im|) ^ N * Real.exp (ρ * |μ.im|) * |s.im| ^ N * Real.exp (-ρ * |s.im|) := by ring

private theorem lowerRate_of_zLower {g : ℂ → ℂ} {ρ : ℝ} (hg : ZLower g ρ) (hρ : 0 ≤ ρ) (σ₁ σ₂ : ℝ) (μ : ℂ) :
    LowerRate σ₁ σ₂ (fun s => g (1 - s + μ)) ρ := by
  obtain ⟨B, N, hB, h⟩ := hg (1 - σ₂ + μ.re) (1 - σ₁ + μ.re)
  refine ⟨Real.exp (ρ * |μ.im|) * B * (2 + |μ.im|) ^ N, 2 + |μ.im|, N, by positivity,
    by linarith [abs_nonneg μ.im], fun s hs₁ hs₂ hs => ?_⟩
  have hre : (1 - s + μ).re = 1 - s.re + μ.re := by
    rw [Complex.add_re, Complex.sub_re, Complex.one_re]
  have him : (1 - s + μ).im = -s.im + μ.im := by
    rw [Complex.add_im, Complex.sub_im, Complex.one_im]
    ring
  obtain ⟨hlo, hhi⟩ := abs_shift_facts (-s.im) μ.im
  rw [← him, abs_neg] at hlo hhi
  have ht : 1 ≤ |s.im| := by linarith [abs_nonneg μ.im]
  have hz := h (1 - s + μ) (by rw [hre]; linarith) (by rw [hre]; linarith) (by linarith)
  have hpow : (1 + |(1 - s + μ).im|) ^ N ≤ (2 + |μ.im|) ^ N * |s.im| ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_abs_shift_le ht hhi) N
  have hexp : Real.exp (-ρ * |s.im|) ≤ Real.exp (ρ * |μ.im|) * Real.exp (-ρ * |(1 - s + μ).im|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hhi hρ
    linarith
  calc Real.exp (-ρ * |s.im|) ≤ Real.exp (ρ * |μ.im|) * Real.exp (-ρ * |(1 - s + μ).im|) := hexp
    _ ≤ Real.exp (ρ * |μ.im|) * (B * (1 + |(1 - s + μ).im|) ^ N * ‖g (1 - s + μ)‖) :=
        mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
    _ ≤ Real.exp (ρ * |μ.im|) * (B * ((2 + |μ.im|) ^ N * |s.im| ^ N) * ‖g (1 - s + μ)‖) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hB) (norm_nonneg _)
    _ = Real.exp (ρ * |μ.im|) * B * (2 + |μ.im|) ^ N * |s.im| ^ N * ‖g (1 - s + μ)‖ := by ring

private theorem pi_div_four_nonneg : (0 : ℝ) ≤ Real.pi / 4 := by positivity

private theorem pi_div_two_nonneg : (0 : ℝ) ≤ Real.pi / 2 := by positivity

private theorem exists_forall_norm_prod_le_pow_mul_norm_prod (hS : StirlingInput) (gR gC gRd gCd : Multiset ℂ)
    (hcard : Multiset.card gRd + 2 * Multiset.card gCd ≤ Multiset.card gR + 2 * Multiset.card gC)
    (σ₁ σ₂ : ℝ) :
    ∃ (C T₀ : ℝ) (k : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
      ‖(gR.map fun μ => Complex.Gammaℝ (s + μ)).prod * (gC.map fun μ => Complex.Gammaℂ (s + μ)).prod‖ ≤
        C * |s.im| ^ k *
          ‖(gRd.map fun μ => Complex.Gammaℝ (1 - s + μ)).prod *
            (gCd.map fun μ => Complex.Gammaℂ (1 - s + μ)).prod‖ := by
  have hU : UpperRate σ₁ σ₂
      (fun s => (gR.map fun μ => Complex.Gammaℝ (s + μ)).prod * (gC.map fun μ => Complex.Gammaℂ (s + μ)).prod)
      (Real.pi / 4 * Multiset.card gR + Real.pi / 2 * Multiset.card gC) :=
    (upperRate_multiset_prod (fun μ s => Complex.Gammaℝ (s + μ)) gR fun μ _ =>
        upperRate_of_zUpper (zUpper_Gammaℝ hS) pi_div_four_nonneg σ₁ σ₂ μ).mul
      (upperRate_multiset_prod (fun μ s => Complex.Gammaℂ (s + μ)) gC fun μ _ =>
        upperRate_of_zUpper (zUpper_Gammaℂ hS) pi_div_two_nonneg σ₁ σ₂ μ)
  have hL : LowerRate σ₁ σ₂
      (fun s => (gRd.map fun μ => Complex.Gammaℝ (1 - s + μ)).prod *
        (gCd.map fun μ => Complex.Gammaℂ (1 - s + μ)).prod)
      (Real.pi / 4 * Multiset.card gRd + Real.pi / 2 * Multiset.card gCd) :=
    (lowerRate_multiset_prod (fun μ s => Complex.Gammaℝ (1 - s + μ)) gRd fun μ _ =>
        lowerRate_of_zLower (zLower_Gammaℝ hS) pi_div_four_nonneg σ₁ σ₂ μ).mul
      (lowerRate_multiset_prod (fun μ s => Complex.Gammaℂ (1 - s + μ)) gCd fun μ _ =>
        lowerRate_of_zLower (zLower_Gammaℂ hS) pi_div_two_nonneg σ₁ σ₂ μ)
  have hc : (Multiset.card gRd : ℝ) + 2 * Multiset.card gCd ≤ Multiset.card gR + 2 * Multiset.card gC := by
    exact_mod_cast hcard
  have hrate : Real.pi / 4 * Multiset.card gRd + Real.pi / 2 * Multiset.card gCd ≤
      Real.pi / 4 * Multiset.card gR + Real.pi / 2 * Multiset.card gC := by
    have := mul_le_mul_of_nonneg_left hc pi_div_four_nonneg
    linarith
  obtain ⟨B₁, T₁, N₁, hB₁, _, h₁⟩ := hU
  obtain ⟨B₂, T₂, N₂, _, _, h₂⟩ := hL.mono_rate hrate
  refine ⟨B₁ * B₂, max T₁ T₂, N₁ + N₂, fun s hs₁ hs₂ hs => ?_⟩
  have e₁ := h₁ s hs₁ hs₂ (le_trans (le_max_left _ _) hs)
  have e₂ := h₂ s hs₁ hs₂ (le_trans (le_max_right _ _) hs)
  calc ‖(gR.map fun μ => Complex.Gammaℝ (s + μ)).prod * (gC.map fun μ => Complex.Gammaℂ (s + μ)).prod‖
      ≤ B₁ * |s.im| ^ N₁ *
          Real.exp (-(Real.pi / 4 * Multiset.card gR + Real.pi / 2 * Multiset.card gC) * |s.im|) := e₁
    _ ≤ B₁ * |s.im| ^ N₁ * (B₂ * |s.im| ^ N₂ *
          ‖(gRd.map fun μ => Complex.Gammaℝ (1 - s + μ)).prod * (gCd.map fun μ => Complex.Gammaℂ (1 - s + μ)).prod‖) :=
        mul_le_mul_of_nonneg_left e₂ (by positivity)
    _ = B₁ * B₂ * |s.im| ^ (N₁ + N₂) *
          ‖(gRd.map fun μ => Complex.Gammaℝ (1 - s + μ)).prod *
            (gCd.map fun μ => Complex.Gammaℂ (1 - s + μ)).prod‖ := by
        rw [pow_add]
        ring

end GammaRatioStrip

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "signEpsilon RealArchParam signShift RealArchParam.gammaR RealArchParam.gammaC RealArchParam.archFactor RealArchParam.twist RealArchParam.dual RealArchParam.twist_twist RealArchParam.gammaC_twist RealArchParam.gammaR_twist_zero RealArchParam.discrete RealArchParam.principal LDatum LDatum.archFactor LDatum.archFactorDual CubicLambda.lambdaArch CubicInduction.IsArchZeta30ConvergentAbove CubicInduction.IsArchZeta31ConvergentAbove HeckeTate.heckeDatum CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous CubicInduction.jacquetVector3_isArchZetaConvergentAbove CubicInduction.isGL3PsiWhittakerFn_jacquetVector3 CubicInduction.jacquetVector3_scalar_mul CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar CubicInduction.heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR CubicInduction.heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq CubicInduction.isKFinite_jacquetVector3 CubicInduction.jacquetVector3_norm_archComponent3_le CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul CubicInduction.forall_pow_mul_norm_archZeta30_jacquetVector3_le CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" namespace LDatum p2m_export "LanglandsTunnell.LDatum" "archFactor archFactorDual norm gammaCDual dual degree mk gammaC gammaR gammaRDual abscissa" end LanglandsTunnell.LDatum
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.LDatum" in

private theorem LanglandsTunnell.LDatum.exists_forall_norm_archFactor_le_pow_mul_norm_archFactorDual
    {ι : Type*} (D : LanglandsTunnell.LDatum ι)
    (hcard : Multiset.card D.gammaRDual + 2 * Multiset.card D.gammaCDual ≤
      Multiset.card D.gammaR + 2 * Multiset.card D.gammaC)
    (σ₁ σ₂ : ℝ) :
    ∃ (C T₀ : ℝ) (k : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
      ‖D.archFactor s‖ ≤ C * |s.im| ^ k * ‖D.archFactorDual (1 - s)‖ := by
  obtain ⟨C, T₀, k, h⟩ := GammaRatioStrip.exists_forall_norm_prod_le_pow_mul_norm_prod
    Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
    D.gammaR D.gammaC D.gammaRDual D.gammaCDual hcard σ₁ σ₂
  refine ⟨C, T₀, k, fun s hs₁ hs₂ hs => ?_⟩
  simpa only [LanglandsTunnell.LDatum.archFactor, LanglandsTunnell.LDatum.archFactorDual] using h s hs₁ hs₂ hs

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "signEpsilon RealArchParam signShift RealArchParam.gammaR RealArchParam.gammaC RealArchParam.archFactor RealArchParam.twist RealArchParam.dual RealArchParam.twist_twist RealArchParam.gammaC_twist RealArchParam.gammaR_twist_zero RealArchParam.discrete RealArchParam.principal LDatum LDatum.archFactor LDatum.archFactorDual CubicLambda.lambdaArch CubicInduction.IsArchZeta30ConvergentAbove CubicInduction.IsArchZeta31ConvergentAbove HeckeTate.heckeDatum CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous CubicInduction.jacquetVector3_isArchZetaConvergentAbove CubicInduction.isGL3PsiWhittakerFn_jacquetVector3 CubicInduction.jacquetVector3_scalar_mul CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar CubicInduction.heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR CubicInduction.heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq CubicInduction.isKFinite_jacquetVector3 CubicInduction.jacquetVector3_norm_archComponent3_le CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul CubicInduction.forall_pow_mul_norm_archZeta30_jacquetVector3_le CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" namespace HeckeTate p2m_export "LanglandsTunnell.HeckeTate" "heckeDatum" end LanglandsTunnell.HeckeTate
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.HeckeTate" in

private theorem LanglandsTunnell.HeckeTate.card_gammaRDual_heckeDatum_add_eq
    (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace F, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace F, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace F, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ) :
    Multiset.card (LanglandsTunnell.HeckeTate.heckeDatum F χ uR aR uC kC).gammaRDual +
        2 * Multiset.card (LanglandsTunnell.HeckeTate.heckeDatum F χ uR aR uC kC).gammaCDual =
      Multiset.card (LanglandsTunnell.HeckeTate.heckeDatum F χ uR aR uC kC).gammaR +
        2 * Multiset.card (LanglandsTunnell.HeckeTate.heckeDatum F χ uR aR uC kC).gammaC := by
  simp only [LanglandsTunnell.HeckeTate.heckeDatum, Multiset.card_sum, Multiset.card_singleton]

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "signEpsilon RealArchParam signShift RealArchParam.gammaR RealArchParam.gammaC RealArchParam.archFactor RealArchParam.twist RealArchParam.dual RealArchParam.twist_twist RealArchParam.gammaC_twist RealArchParam.gammaR_twist_zero RealArchParam.discrete RealArchParam.principal LDatum LDatum.archFactor LDatum.archFactorDual CubicLambda.lambdaArch CubicInduction.IsArchZeta30ConvergentAbove CubicInduction.IsArchZeta31ConvergentAbove HeckeTate.heckeDatum CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous CubicInduction.jacquetVector3_isArchZetaConvergentAbove CubicInduction.isGL3PsiWhittakerFn_jacquetVector3 CubicInduction.jacquetVector3_scalar_mul CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar CubicInduction.heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR CubicInduction.heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq CubicInduction.isKFinite_jacquetVector3 CubicInduction.jacquetVector3_norm_archComponent3_le CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul CubicInduction.forall_pow_mul_norm_archZeta30_jacquetVector3_le CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" namespace CubicInduction p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 dualWhittakerFn3 weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsKFinite AdelicGL iotaGL archComponent3 diagUnitGL2 archRoot₁ archRoot₂ archRootSum archZeta31 archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove polyGauss3 jacquetVector3 jacquetIntegrand3_integrable_and_jacquetVector3_continuous jacquetVector3_isArchZetaConvergentAbove isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul re_eq_zero_of_isArchCompAt_of_isUnitaryChar heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR archZeta30_jacquetVector3_eq_archFactor_mul archZetaDual31_jacquetVector3_mul_archFactor_eq isKFinite_jacquetVector3 jacquetVector3_norm_archComponent3_le exists_differentiable_unfoldingIntegral_eq_GammaR_mul forall_pow_mul_norm_archZeta30_jacquetVector3_le forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" end LanglandsTunnell.CubicInduction
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.forall_exists_pow_mul_norm_le_of_strips_union
    (f : ℂ → ℂ) (σ₁ σ₂ σ₃ : ℝ)
    (h₁₂ : ∀ N : ℕ, ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| → |s.im| ^ N * ‖f s‖ ≤ C)
    (h₂₃ : ∀ N : ℕ, ∃ C T₀ : ℝ, ∀ s : ℂ, σ₂ ≤ s.re → s.re ≤ σ₃ → T₀ ≤ |s.im| → |s.im| ^ N * ‖f s‖ ≤ C) :
    ∀ N : ℕ, ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₃ → T₀ ≤ |s.im| → |s.im| ^ N * ‖f s‖ ≤ C := by
  intro N
  obtain ⟨C₁, T₁, h₁⟩ := h₁₂ N
  obtain ⟨C₂, T₂, h₂⟩ := h₂₃ N
  refine ⟨max C₁ C₂, max T₁ T₂, fun s hs₁ hs₃ hT => ?_⟩
  rcases le_total s.re σ₂ with h | h
  · exact (h₁ s hs₁ h (le_trans (le_max_left _ _) hT)).trans (le_max_left _ _)
  · exact (h₂ s h hs₃ (le_trans (le_max_right _ _) hT)).trans (le_max_right _ _)

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "signEpsilon RealArchParam signShift RealArchParam.gammaR RealArchParam.gammaC RealArchParam.archFactor RealArchParam.twist RealArchParam.dual RealArchParam.twist_twist RealArchParam.gammaC_twist RealArchParam.gammaR_twist_zero RealArchParam.discrete RealArchParam.principal LDatum LDatum.archFactor LDatum.archFactorDual CubicLambda.lambdaArch CubicInduction.IsArchZeta30ConvergentAbove CubicInduction.IsArchZeta31ConvergentAbove HeckeTate.heckeDatum CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous CubicInduction.jacquetVector3_isArchZetaConvergentAbove CubicInduction.isGL3PsiWhittakerFn_jacquetVector3 CubicInduction.jacquetVector3_scalar_mul CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar CubicInduction.heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR CubicInduction.heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq CubicInduction.isKFinite_jacquetVector3 CubicInduction.jacquetVector3_norm_archComponent3_le CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul CubicInduction.forall_pow_mul_norm_archZeta30_jacquetVector3_le CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" namespace CubicInduction p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 dualWhittakerFn3 weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsKFinite AdelicGL iotaGL archComponent3 diagUnitGL2 archRoot₁ archRoot₂ archRootSum archZeta31 archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove polyGauss3 jacquetVector3 jacquetIntegrand3_integrable_and_jacquetVector3_continuous jacquetVector3_isArchZetaConvergentAbove isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul re_eq_zero_of_isArchCompAt_of_isUnitaryChar heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR archZeta30_jacquetVector3_eq_archFactor_mul archZetaDual31_jacquetVector3_mul_archFactor_eq isKFinite_jacquetVector3 jacquetVector3_norm_archComponent3_le exists_differentiable_unfoldingIntegral_eq_GammaR_mul forall_pow_mul_norm_archZeta30_jacquetVector3_le forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" namespace IsArchZeta30ConvergentAbove end LanglandsTunnell.CubicInduction.IsArchZeta30ConvergentAbove
namespace LanglandsTunnell.CubicInduction.IsArchZeta30ConvergentAbove
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem _root_.LanglandsTunnell.CubicInduction.IsArchZeta30ConvergentAbove.mono
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    {μ : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ} {W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ}
    {σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ} {g : GL (Fin 3) (InfiniteAdeleRing ℚ)} {σ₀ σ₀' : ℝ}
    (h : IsArchZeta30ConvergentAbove μ W σ g σ₀) (hle : σ₀ ≤ σ₀') : IsArchZeta30ConvergentAbove μ W σ g σ₀' := by
  unfold IsArchZeta30ConvergentAbove at h ⊢
  exact fun s hs => h s (lt_of_le_of_lt hle hs)

end LanglandsTunnell.CubicInduction.IsArchZeta30ConvergentAbove
p2m_export "" "LanglandsTunnell.CubicInduction.IsArchZeta30ConvergentAbove.mono"
namespace LanglandsTunnell p2m_export "LanglandsTunnell" "signEpsilon RealArchParam signShift RealArchParam.gammaR RealArchParam.gammaC RealArchParam.archFactor RealArchParam.twist RealArchParam.dual RealArchParam.twist_twist RealArchParam.gammaC_twist RealArchParam.gammaR_twist_zero RealArchParam.discrete RealArchParam.principal LDatum LDatum.archFactor LDatum.archFactorDual CubicLambda.lambdaArch CubicInduction.IsArchZeta30ConvergentAbove CubicInduction.IsArchZeta31ConvergentAbove HeckeTate.heckeDatum CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous CubicInduction.jacquetVector3_isArchZetaConvergentAbove CubicInduction.isGL3PsiWhittakerFn_jacquetVector3 CubicInduction.jacquetVector3_scalar_mul CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar CubicInduction.heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR CubicInduction.heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq CubicInduction.isKFinite_jacquetVector3 CubicInduction.jacquetVector3_norm_archComponent3_le CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul CubicInduction.forall_pow_mul_norm_archZeta30_jacquetVector3_le CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" namespace CubicInduction p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 dualWhittakerFn3 weylPrime3 IsGL3PsiWhittakerFn transposeInv3 IsKFinite AdelicGL iotaGL archComponent3 diagUnitGL2 archRoot₁ archRoot₂ archRootSum archZeta31 archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove polyGauss3 jacquetVector3 jacquetIntegrand3_integrable_and_jacquetVector3_continuous jacquetVector3_isArchZetaConvergentAbove isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul re_eq_zero_of_isArchCompAt_of_isUnitaryChar heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR archZeta30_jacquetVector3_eq_archFactor_mul archZetaDual31_jacquetVector3_mul_archFactor_eq isKFinite_jacquetVector3 jacquetVector3_norm_archComponent3_le exists_differentiable_unfoldingIntegral_eq_GammaR_mul forall_pow_mul_norm_archZeta30_jacquetVector3_le forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" namespace IsArchZeta31ConvergentAbove end LanglandsTunnell.CubicInduction.IsArchZeta31ConvergentAbove
namespace LanglandsTunnell.CubicInduction.IsArchZeta31ConvergentAbove
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem _root_.LanglandsTunnell.CubicInduction.IsArchZeta31ConvergentAbove.mono
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    {μ : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ} {ν : MeasureTheory.Measure (InfiniteAdeleRing ℚ)}
    {W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ} {σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ}
    {g : GL (Fin 3) (InfiniteAdeleRing ℚ)} {σ₀ σ₀' : ℝ}
    (h : IsArchZeta31ConvergentAbove μ ν W σ g σ₀) (hle : σ₀ ≤ σ₀') :
    IsArchZeta31ConvergentAbove μ ν W σ g σ₀' := by
  unfold IsArchZeta31ConvergentAbove at h ⊢
  exact fun s hs => h s (lt_of_le_of_lt hle hs)

end LanglandsTunnell.CubicInduction.IsArchZeta31ConvergentAbove
p2m_export "" "LanglandsTunnell.CubicInduction.IsArchZeta31ConvergentAbove.mono"
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.eq_mul_mul_of_eq_mul_mul_of_mul_eq (Z κ F X Γ P : ℂ)
    (hZ : Z = κ * F * X) (hX : κ * X = Γ * P) : Z = P * (F * Γ) := by
  rw [hZ]
  linear_combination F * hX

section AssemblyZetaHolomorphy

open NumberField MeasureTheory

namespace ZetaHolomorphy

private theorem rpow_mul_abs_log_le {r ε t u : ℝ} (hr : 0 < r) (hε : 0 < ε) (hu : |u - t| ≤ ε) :
    r ^ (u - 1) * |Real.log r| ≤ (2 / ε) * (r ^ (t + 2 * ε - 1) + r ^ (t - 2 * ε - 1)) := by
  have hu' := abs_le.1 hu
  have hε' : 0 < 2 / ε := by positivity
  have hp1 : 0 ≤ r ^ (t + 2 * ε - 1) := (Real.rpow_pos_of_pos hr _).le
  have hp2 : 0 ≤ r ^ (t - 2 * ε - 1) := (Real.rpow_pos_of_pos hr _).le
  rcases le_or_gt 1 r with h1 | h1
  ·
    have hlog : |Real.log r| ≤ r ^ ε / ε := by
      rw [abs_of_nonneg (Real.log_nonneg h1)]
      exact Real.log_le_rpow_div hr.le hε
    have hpow : r ^ (u - 1) ≤ r ^ (t + ε - 1) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hu'.2])
    calc r ^ (u - 1) * |Real.log r| ≤ r ^ (t + ε - 1) * (r ^ ε / ε) :=
          mul_le_mul hpow hlog (abs_nonneg _) (Real.rpow_pos_of_pos hr _).le
      _ = (1 / ε) * r ^ (t + 2 * ε - 1) := by
          rw [show t + 2 * ε - 1 = (t + ε - 1) + ε by ring, Real.rpow_add hr]; ring
      _ ≤ (2 / ε) * (r ^ (t + 2 * ε - 1) + r ^ (t - 2 * ε - 1)) := by
          have h2 : 1 / ε ≤ 2 / ε := by
            rw [div_le_div_iff_of_pos_right hε]; norm_num
          nlinarith [mul_le_mul_of_nonneg_right h2 hp1, mul_nonneg hε'.le hp2]
  ·
    have hlog : |Real.log r| ≤ r ^ (-ε) / ε := by
      rw [abs_of_nonpos (Real.log_nonpos hr.le h1.le), ← Real.log_inv, Real.rpow_neg hr.le,
        ← Real.inv_rpow hr.le]
      exact Real.log_le_rpow_div (inv_nonneg.2 hr.le) hε
    have hpow : r ^ (u - 1) ≤ r ^ (t - ε - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hr h1.le (by linarith [hu'.1])
    calc r ^ (u - 1) * |Real.log r| ≤ r ^ (t - ε - 1) * (r ^ (-ε) / ε) :=
          mul_le_mul hpow hlog (abs_nonneg _) (Real.rpow_pos_of_pos hr _).le
      _ = (1 / ε) * r ^ (t - 2 * ε - 1) := by
          rw [show t - 2 * ε - 1 = (t - ε - 1) + -ε by ring, Real.rpow_add hr]; ring
      _ ≤ (2 / ε) * (r ^ (t + 2 * ε - 1) + r ^ (t - 2 * ε - 1)) := by
          have h2 : 1 / ε ≤ 2 / ε := by
            rw [div_le_div_iff_of_pos_right hε]; norm_num
          nlinarith [mul_le_mul_of_nonneg_right h2 hp2, mul_nonneg hε'.le hp1]

private theorem integrable_integral_mul_mul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] (w : α → β → ℂ) (c q : α → ℂ)
    (h : Integrable (fun p : α × β => w p.1 p.2 * c p.1 * q p.1) (μ.prod ν)) :
    Integrable (fun a => (∫ x, w a x ∂ν) * c a * q a) μ := by
  have h' := h.integral_prod_left
  refine h'.congr (Filter.Eventually.of_forall fun a => ?_)
  show ∫ y, w a y * c a * q a ∂ν = (∫ x, w a x ∂ν) * c a * q a
  have e1 : ∫ y, w a y * c a * q a ∂ν = (∫ y, w a y * c a ∂ν) * q a :=
    integral_mul_const (q a) (fun y => w a y * c a)
  have e2 : ∫ y, w a y * c a ∂ν = (∫ y, w a y ∂ν) * c a := integral_mul_const (c a) (fun y => w a y)
  rw [e1, e2]

private theorem differentiableOn_integral_mul_cpow {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c : α → ℂ) (r : α → ℝ) (hr : ∀ a, 0 < r a) (hr_meas : Measurable r) (σ₀ : ℝ)
    (hint : ∀ s : ℂ, σ₀ < s.re → Integrable (fun a => c a * ((r a : ℝ) : ℂ) ^ (s - 1)) μ) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ a, c a * ((r a : ℝ) : ℂ) ^ (s - 1) ∂μ) {s : ℂ | σ₀ < s.re} := by
  intro s₁ hs₁
  have hs₁' : σ₀ < s₁.re := hs₁
  apply DifferentiableAt.differentiableWithinAt
  set ε : ℝ := (s₁.re - σ₀) / 4 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  set tp : ℝ := s₁.re + 2 * ε with htp
  set tm : ℝ := s₁.re - 2 * ε with htm
  have htp_mem : σ₀ < ((tp : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith
  have htm_mem : σ₀ < ((tm : ℝ) : ℂ).re := by rw [Complex.ofReal_re, htm, hε_def]; linarith
  have hrne : ∀ a, ((r a : ℝ) : ℂ) ≠ 0 := fun a => Complex.ofReal_ne_zero.2 (hr a).ne'
  have hball : Metric.ball s₁ ε ∈ nhds s₁ := Metric.ball_mem_nhds s₁ hε
  have hre : ∀ s ∈ Metric.ball s₁ ε, |s.re - s₁.re| ≤ ε := by
    intro s hs
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have := Complex.abs_re_le_norm (s - s₁)
    rw [Complex.sub_re] at this
    exact this.trans hs.le
  have hlog : AEStronglyMeasurable (fun a => Complex.log ((r a : ℝ) : ℂ)) μ :=
    ((Complex.continuous_ofReal.measurable.comp hr_meas).clog).aestronglyMeasurable
  have hnorm : ∀ (s : ℂ) (a : α),
      ‖c a * ((r a : ℝ) : ℂ) ^ (s - 1) * Complex.log ((r a : ℝ) : ℂ)‖ =
        ‖c a‖ * (r a ^ (s.re - 1) * |Real.log (r a)|) := by
    intro s a
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hr a), ← Complex.ofReal_log (hr a).le,
      Complex.norm_real, Real.norm_eq_abs, mul_assoc, Complex.sub_re, Complex.one_re]
  have hnorm_t : ∀ (t : ℝ) (a : α),
      ‖c a * ((r a : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) - 1)‖ = ‖c a‖ * r a ^ (t - 1) := by
    intro t a
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hr a), Complex.sub_re, Complex.ofReal_re,
      Complex.one_re]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s₁)
    (F := fun s a => c a * ((r a : ℝ) : ℂ) ^ (s - 1))
    (F' := fun s a => c a * ((r a : ℝ) : ℂ) ^ (s - 1) * Complex.log ((r a : ℝ) : ℂ))
    (bound := fun a => (2 / ε) * (‖c a * ((r a : ℝ) : ℂ) ^ (((tp : ℝ) : ℂ) - 1)‖ +
      ‖c a * ((r a : ℝ) : ℂ) ^ (((tm : ℝ) : ℂ) - 1)‖))
    hball ?_ (hint s₁ hs₁') ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt
  ·
    have hopen : {s : ℂ | σ₀ < s.re} ∈ nhds s₁ :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs₁'
    exact Filter.eventually_of_mem hopen fun s hs => (hint s hs).aestronglyMeasurable
  · exact (hint s₁ hs₁').aestronglyMeasurable.mul hlog
  · refine Filter.Eventually.of_forall fun a s hs => ?_
    rw [hnorm, hnorm_t, hnorm_t]
    have hb := rpow_mul_abs_log_le (hr a) hε (hre s hs)
    calc ‖c a‖ * (r a ^ (s.re - 1) * |Real.log (r a)|)
        ≤ ‖c a‖ * ((2 / ε) * (r a ^ (s₁.re + 2 * ε - 1) + r a ^ (s₁.re - 2 * ε - 1))) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (2 / ε) * (‖c a‖ * r a ^ (tp - 1) + ‖c a‖ * r a ^ (tm - 1)) := by rw [htp, htm]; ring
  · exact (((hint _ htp_mem).norm.add (hint _ htm_mem).norm).const_mul (2 / ε))
  · refine Filter.Eventually.of_forall fun a s _ => ?_
    have hd : HasDerivAt (fun s : ℂ => ((r a : ℝ) : ℂ) ^ (s - 1))
        (((r a : ℝ) : ℂ) ^ (s - 1) * Complex.log ((r a : ℝ) : ℂ) * 1) s :=
      ((hasDerivAt_id s).sub_const 1).const_cpow (Or.inl (hrne a))
    have := hd.const_mul (c a)
    refine this.congr_deriv ?_
    ring

private theorem norm_units_pos (a : (InfiniteAdeleRing ℚ)ˣ) : 0 < ‖(a : InfiniteAdeleRing ℚ)‖ := by
  rw [InfiniteAdeleRing.norm_def]
  exact Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 ((Pi.isUnit_iff.1 a.isUnit v).ne_zero)) _

private theorem continuous_norm_infiniteAdeleRing : Continuous fun x : InfiniteAdeleRing ℚ => ‖x‖ := by
  simp only [InfiniteAdeleRing.norm_def]
  exact continuous_finsetProd _ fun v _ => (continuous_apply v).norm.pow _

end ZetaHolomorphy

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.differentiableOn_archZeta31_of_isArchZeta31ConvergentAbove
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (μ : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) (ν : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    [MeasureTheory.SFinite ν]
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ₀ : ℝ) (h : IsArchZeta31ConvergentAbove μ ν W σ g σ₀) :
    DifferentiableOn ℂ (fun s : ℂ => archZeta31 μ ν W σ s g) {s : ℂ | σ₀ < s.re} := by
  unfold archZeta31
  refine ZetaHolomorphy.differentiableOn_integral_mul_cpow μ
    (fun a => (∫ x : InfiniteAdeleRing ℚ, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) *
      ((σ a : ℂˣ) : ℂ))
    (fun a => ‖(a : InfiniteAdeleRing ℚ)‖) ZetaHolomorphy.norm_units_pos
    (ZetaHolomorphy.continuous_norm_infiniteAdeleRing.comp Units.continuous_val).measurable σ₀ ?_
  intro s hs
  exact ZetaHolomorphy.integrable_integral_mul_mul μ ν
    (fun a x => W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g)) (fun a => ((σ a : ℂˣ) : ℂ))
    (fun a => ((‖(a : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) (h s hs)

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.differentiableOn_archZeta30_of_isArchZeta30ConvergentAbove
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (μ : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ)
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ₀ : ℝ) (h : IsArchZeta30ConvergentAbove μ W σ g σ₀) :
    DifferentiableOn ℂ (fun s : ℂ => archZeta30 μ W σ s g) {s : ℂ | σ₀ < s.re} := by
  unfold archZeta30
  exact ZetaHolomorphy.differentiableOn_integral_mul_cpow μ
    (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((σ a : ℂˣ) : ℂ)) (fun a => ‖(a : InfiniteAdeleRing ℚ)‖)
    ZetaHolomorphy.norm_units_pos
    (ZetaHolomorphy.continuous_norm_infiniteAdeleRing.comp Units.continuous_val).measurable σ₀ h

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.eqOn_halfPlane_lt_re_of_eqOn_strip (f g : ℂ → ℂ) (b σ₁ σ₂ : ℝ)
    (hb₁ : b ≤ σ₁) (h₁₂ : σ₁ < σ₂)
    (hf : DifferentiableOn ℂ f {s : ℂ | b < s.re}) (hg : DifferentiableOn ℂ g {s : ℂ | b < s.re})
    (heq : ∀ s : ℂ, σ₁ < s.re → s.re < σ₂ → f s = g s) :
    Set.EqOn f g {s : ℂ | b < s.re} := by
  have hU : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | b < s.re} := (convex_halfSpace_re_gt b).isPreconnected
  set z₀ : ℂ := (((σ₁ + σ₂) / 2 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = (σ₁ + σ₂) / 2 := by simp [hz₀]
  have hz₀U : z₀ ∈ {s : ℂ | b < s.re} := by
    show b < z₀.re
    rw [hz₀re]; linarith
  have hnhds : f =ᶠ[nhds z₀] g := by
    have hV : IsOpen {s : ℂ | σ₁ < s.re ∧ s.re < σ₂} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hzV : z₀ ∈ {s : ℂ | σ₁ < s.re ∧ s.re < σ₂} := by
      refine ⟨?_, ?_⟩ <;> · show _ ; rw [hz₀re]; linarith
    filter_upwards [hV.mem_nhds hzV] with s hs using heq s hs.1 hs.2
  exact (hf.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hU) hconn hz₀U hnhds

end AssemblyZetaHolomorphy

namespace LanglandsTunnell.LDatum
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.LDatum" in

private theorem _root_.LanglandsTunnell.LDatum.archFactor_ne_zero_of_forall_re_pos {ι : Type*} (D : LanglandsTunnell.LDatum ι) (s : ℂ)
    (hR : ∀ μ ∈ D.gammaR, 0 < (s + μ).re) (hC : ∀ μ ∈ D.gammaC, 0 < (s + μ).re) : D.archFactor s ≠ 0 := by
  rw [LanglandsTunnell.LDatum.archFactor]
  refine mul_ne_zero (Multiset.prod_ne_zero ?_) (Multiset.prod_ne_zero ?_)
  · intro h
    obtain ⟨μ, hμ, h0⟩ := Multiset.mem_map.mp h
    exact Complex.Gammaℝ_ne_zero_of_re_pos (hR μ hμ) h0
  · intro h
    obtain ⟨μ, hμ, h0⟩ := Multiset.mem_map.mp h
    have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    refine (mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos (hC μ hμ))) h0
    intro hz
    rw [Complex.cpow_eq_zero_iff] at hz
    exact h2π hz.1

end LanglandsTunnell.LDatum
p2m_export "" "LanglandsTunnell.LDatum.archFactor_ne_zero_of_forall_re_pos"
namespace LanglandsTunnell p2m_export "LanglandsTunnell" "signEpsilon RealArchParam signShift RealArchParam.gammaR RealArchParam.gammaC RealArchParam.archFactor RealArchParam.twist RealArchParam.dual RealArchParam.twist_twist RealArchParam.gammaC_twist RealArchParam.gammaR_twist_zero RealArchParam.discrete RealArchParam.principal LDatum LDatum.archFactor LDatum.archFactorDual CubicLambda.lambdaArch CubicInduction.IsArchZeta30ConvergentAbove CubicInduction.IsArchZeta31ConvergentAbove HeckeTate.heckeDatum CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous CubicInduction.jacquetVector3_isArchZetaConvergentAbove CubicInduction.isGL3PsiWhittakerFn_jacquetVector3 CubicInduction.jacquetVector3_scalar_mul CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar CubicInduction.heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR CubicInduction.heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq CubicInduction.isKFinite_jacquetVector3 CubicInduction.jacquetVector3_norm_archComponent3_le CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul CubicInduction.forall_pow_mul_norm_archZeta30_jacquetVector3_le CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" end LanglandsTunnell
p2m_open_scoped "LanglandsTunnell" in

private theorem LanglandsTunnell.signEpsilon_ne_zero (a : ZMod 2) : LanglandsTunnell.signEpsilon a ≠ 0 := by
  unfold LanglandsTunnell.signEpsilon
  split_ifs
  · exact one_ne_zero
  · exact Complex.I_ne_zero

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "signEpsilon RealArchParam signShift RealArchParam.gammaR RealArchParam.gammaC RealArchParam.archFactor RealArchParam.twist RealArchParam.dual RealArchParam.twist_twist RealArchParam.gammaC_twist RealArchParam.gammaR_twist_zero RealArchParam.discrete RealArchParam.principal LDatum LDatum.archFactor LDatum.archFactorDual CubicLambda.lambdaArch CubicInduction.IsArchZeta30ConvergentAbove CubicInduction.IsArchZeta31ConvergentAbove HeckeTate.heckeDatum CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous CubicInduction.jacquetVector3_isArchZetaConvergentAbove CubicInduction.isGL3PsiWhittakerFn_jacquetVector3 CubicInduction.jacquetVector3_scalar_mul CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar CubicInduction.heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR CubicInduction.heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq CubicInduction.isKFinite_jacquetVector3 CubicInduction.jacquetVector3_norm_archComponent3_le CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul CubicInduction.forall_pow_mul_norm_archZeta30_jacquetVector3_le CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" namespace CubicLambda p2m_export "LanglandsTunnell.CubicLambda" "lambdaArch" end LanglandsTunnell.CubicLambda
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicLambda" in

private theorem LanglandsTunnell.CubicLambda.lambdaArch_ne_zero (K : Type) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) : LanglandsTunnell.CubicLambda.lambdaArch K w ≠ 0 := by
  unfold LanglandsTunnell.CubicLambda.lambdaArch
  split_ifs
  · exact one_ne_zero
  · exact LanglandsTunnell.signEpsilon_ne_zero 1

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.eqOn_halfPlane_re_lt_of_eqOn_strip (f g : ℂ → ℂ) (σ₁ σ₂ b : ℝ)
    (h₁₂ : σ₁ < σ₂) (h₂b : σ₂ ≤ b)
    (hf : DifferentiableOn ℂ f {s : ℂ | s.re < b}) (hg : DifferentiableOn ℂ g {s : ℂ | s.re < b})
    (heq : ∀ s : ℂ, σ₁ < s.re → s.re < σ₂ → f s = g s) :
    Set.EqOn f g {s : ℂ | s.re < b} := by
  have hU : IsOpen {s : ℂ | s.re < b} := isOpen_lt Complex.continuous_re continuous_const
  have hconn : IsPreconnected {s : ℂ | s.re < b} := (convex_halfSpace_re_lt b).isPreconnected
  set z₀ : ℂ := (((σ₁ + σ₂) / 2 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = (σ₁ + σ₂) / 2 := by simp [hz₀]
  have hz₀U : z₀ ∈ {s : ℂ | s.re < b} := by
    show z₀.re < b
    rw [hz₀re]; linarith
  have hnhds : f =ᶠ[nhds z₀] g := by
    have hV : IsOpen {s : ℂ | σ₁ < s.re ∧ s.re < σ₂} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hzV : z₀ ∈ {s : ℂ | σ₁ < s.re ∧ s.re < σ₂} := by
      refine ⟨?_, ?_⟩ <;> · show _ ; rw [hz₀re]; linarith
    filter_upwards [hV.mem_nhds hzV] with s hs using heq s hs.1 hs.2
  exact (hf.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hU) hconn hz₀U hnhds

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.differentiableAt_multiset_prod_Gammaℝ (M : Multiset ℂ) (w : ℂ)
    (h : ∀ μ ∈ M, 0 < (w + μ).re) :
    DifferentiableAt ℂ (fun z : ℂ => (M.map fun μ => Complex.Gammaℝ (z + μ)).prod) w := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have ha : 0 < (w + a).re := h a (Multiset.mem_cons_self a M)
    have hM : ∀ μ ∈ M, 0 < (w + μ).re := fun μ hμ => h μ (Multiset.mem_cons_of_mem hμ)
    have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℝ (z + a)) w := by
      have hpole : ∀ m : ℕ, (w + a) / 2 ≠ -m := by
        intro m hm
        have hre := congrArg Complex.re hm
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        rw [Complex.add_re] at ha
        simp at hre
        linarith
      have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + a) / 2)) w :=
        ((((differentiableAt_id.add (differentiableAt_const a)).neg).div_const 2).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((z + a) / 2)) w :=
        (Complex.differentiableAt_Gamma _ hpole).comp w
          ((differentiableAt_id.add (differentiableAt_const a)).div_const 2)
      have h__af := h1.mul h2
      simp [Complex.Gammaℝ_def] at h__af ⊢
      exact h__af
    have h__af := hΓ.mul (ih hM)
    simp [Multiset.map_cons, Multiset.prod_cons] at h__af ⊢
    exact h__af

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.differentiableAt_multiset_prod_Gammaℂ (M : Multiset ℂ) (w : ℂ)
    (h : ∀ μ ∈ M, 0 < (w + μ).re) :
    DifferentiableAt ℂ (fun z : ℂ => (M.map fun μ => Complex.Gammaℂ (z + μ)).prod) w := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have ha : 0 < (w + a).re := h a (Multiset.mem_cons_self a M)
    have hM : ∀ μ ∈ M, 0 < (w + μ).re := fun μ hμ => h μ (Multiset.mem_cons_of_mem hμ)
    have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℂ (z + a)) w := by
      have hpole : ∀ m : ℕ, (w + a) ≠ -m := by
        intro m hm
        have hre := congrArg Complex.re hm
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        rw [Complex.add_re] at ha
        simp at hre
        linarith
      have h1 : DifferentiableAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-(z + a))) w :=
        (((differentiableAt_id.add (differentiableAt_const a)).neg).const_cpow
          (Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
      have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + a)) w :=
        (Complex.differentiableAt_Gamma _ hpole).comp w (differentiableAt_id.add (differentiableAt_const a))
      have h12 : DifferentiableAt ℂ
          (fun z : ℂ => (2 : ℂ) * ((2 * (Real.pi : ℂ)) ^ (-(z + a)) * Complex.Gamma (z + a))) w :=
        (h1.mul h2).const_mul (2 : ℂ)
      simpa [Complex.Gammaℂ_def, mul_assoc] using h12
    have h__af := hΓ.mul (ih hM)
    simp [Multiset.map_cons, Multiset.prod_cons] at h__af ⊢
    exact h__af

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.LDatum" in

private theorem LanglandsTunnell.LDatum.differentiableOn_archFactorDual {ι : Type*} (D : LanglandsTunnell.LDatum ι) (c : ℝ)
    (hR : ∀ μ ∈ D.gammaRDual, -μ.re ≤ c) (hC : ∀ μ ∈ D.gammaCDual, -μ.re ≤ c) :
    DifferentiableOn ℂ D.archFactorDual {w : ℂ | c < w.re} := by
  intro w hw
  have hw' : c < w.re := hw
  refine DifferentiableAt.differentiableWithinAt ?_
  have h1 := LanglandsTunnell.CubicInduction.differentiableAt_multiset_prod_Gammaℝ D.gammaRDual w
    (fun μ hμ => by have := hR μ hμ; simp only [Complex.add_re]; linarith)
  have h2 := LanglandsTunnell.CubicInduction.differentiableAt_multiset_prod_Gammaℂ D.gammaCDual w
    (fun μ hμ => by have := hC μ hμ; simp only [Complex.add_re]; linarith)
  have : D.archFactorDual = fun z => (D.gammaRDual.map fun μ => Complex.Gammaℝ (z + μ)).prod *
      (D.gammaCDual.map fun μ => Complex.Gammaℂ (z + μ)).prod := by
    funext z; rfl
  rw [this]
  exact h1.mul h2

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.exists_forall_neg_re_lt (M : Multiset ℂ) : ∃ c : ℝ, ∀ μ ∈ M, -μ.re < c := by
  induction M using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons a M ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨max c (-a.re + 1), fun μ hμ => ?_⟩
    rcases Multiset.mem_cons.mp hμ with h | h
    · rw [h]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · exact lt_of_lt_of_le (hc μ h) (le_max_left _ _)

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.exists_forall_twist_neg_re_lt (P : RealArchParam) :
    ∃ c : ℝ, ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c) := by
  obtain ⟨c, hc⟩ := LanglandsTunnell.CubicInduction.exists_forall_neg_re_lt
    ((Finset.univ : Finset (ZMod 2)).val.bind fun a => (P.twist 0 a).gammaR + (P.twist 0 a).gammaC)
  refine ⟨c, fun a => ⟨fun μ hμ => hc μ ?_, fun ν hν => hc ν ?_⟩⟩
  · exact Multiset.mem_bind.mpr ⟨a, Finset.mem_val.mpr (Finset.mem_univ a), Multiset.mem_add.mpr (Or.inl hμ)⟩
  · exact Multiset.mem_bind.mpr ⟨a, Finset.mem_val.mpr (Finset.mem_univ a), Multiset.mem_add.mpr (Or.inr hν)⟩

section AssemblyHaarScalar

open MeasureTheory Set Topology

section HaarScalar

p2m_open "MeasureTheory Measure MeasureTheory.Measure Topology Set"
open scoped ENNReal

namespace ArchUnitsHaar

private noncomputable def lineHaar : Measure ℝ := (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹

private theorem measurable_density : Measurable fun y : ℝ => ENNReal.ofReal |y|⁻¹ :=
  ENNReal.measurable_ofReal.comp continuous_abs.measurable.inv

private theorem lineHaar_singleton_zero : lineHaar ({0} : Set ℝ) = 0 := by
  rw [lineHaar]
  exact withDensity_absolutelyContinuous _ _ Real.volume_singleton

private theorem map_mul_left_lineHaar {c : ℝ} (hc : c ≠ 0) : Measure.map (c * ·) lineHaar = lineHaar := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul c) hs, lineHaar, withDensity_apply _ (measurable_const_mul c hs),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (measurable_const_mul c hs), ← lintegral_indicator hs]
  have key : ∀ y : ℝ, ((c * ·) ⁻¹' s).indicator (fun y : ℝ => ENNReal.ofReal |y|⁻¹) y =
      ENNReal.ofReal |c| * s.indicator (fun z : ℝ => ENNReal.ofReal |z|⁻¹) (c * y) := by
    intro y
    by_cases hy : c * y ∈ s
    · rw [indicator_of_mem (show y ∈ (c * ·) ⁻¹' s from hy), indicator_of_mem hy, ← ENNReal.ofReal_mul (abs_nonneg c),
        abs_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul]
    · rw [indicator_of_notMem (show y ∉ (c * ·) ⁻¹' s from hy), indicator_of_notMem hy, mul_zero]
  simp_rw [key]
  have hmeas : Measurable (s.indicator fun z : ℝ => ENNReal.ofReal |z|⁻¹) := measurable_density.indicator hs
  have hmeas' : Measurable fun y : ℝ => s.indicator (fun z : ℝ => ENNReal.ofReal |z|⁻¹) (c * y) :=
    hmeas.comp (measurable_const_mul c)
  rw [lintegral_const_mul _ hmeas']
  have hsub := lintegral_map (μ := (volume : Measure ℝ)) hmeas (measurable_const_mul c)
  simp only [Real.map_volume_mul_left hc, lintegral_smul_measure, smul_eq_mul] at hsub
  rw [← hsub, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg c), abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hc),
    ENNReal.ofReal_one, one_mul]

section Group

variable {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] {e : G → ℝ}

private noncomputable def pullback (e : G → ℝ) : Measure G := Measure.comap e lineHaar

private theorem pullback_apply (he : IsOpenEmbedding e) (s : Set G) : pullback e s = lineHaar (e '' s) :=
  he.measurableEmbedding.comap_apply _ _

private theorem pullback_isFiniteMeasureOnCompacts (he : IsOpenEmbedding e) (hne : ∀ g : G, e g ≠ 0) :
    IsFiniteMeasureOnCompacts (pullback e) := by
  refine ⟨fun K hK => ?_⟩
  rw [pullback_apply he]
  have hK' : IsCompact (e '' K) := hK.image he.continuous
  rcases (e '' K).eq_empty_or_nonempty with h | h
  · rw [h, measure_empty]; exact ENNReal.zero_lt_top
  obtain ⟨y₀, hy₀K, hy₀⟩ := hK'.exists_isMinOn h continuous_abs.continuousOn
  obtain ⟨g₀, -, rfl⟩ := hy₀K
  have hpos : 0 < |e g₀| := abs_pos.mpr (hne g₀)
  calc lineHaar (e '' K) = ∫⁻ y in e '' K, ENNReal.ofReal |y|⁻¹ := withDensity_apply _ hK'.measurableSet
    _ ≤ ∫⁻ _ in e '' K, ENNReal.ofReal |e g₀|⁻¹ := by
        refine setLIntegral_mono measurable_const fun y hy => ?_
        exact ENNReal.ofReal_le_ofReal (inv_anti₀ hpos (hy₀ hy))
    _ = ENNReal.ofReal |e g₀|⁻¹ * volume (e '' K) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK'.measure_lt_top

private theorem pullback_isOpenPosMeasure (he : IsOpenEmbedding e) (hne : ∀ g : G, e g ≠ 0) :
    IsOpenPosMeasure (pullback e) := by
  refine ⟨fun U hU hUne => ?_⟩
  rw [pullback_apply he, lineHaar, Ne, withDensity_apply_eq_zero measurable_density]
  have hopen : IsOpen (e '' U) := he.isOpenMap U hU
  have hsub : e '' U ⊆ {y : ℝ | ENNReal.ofReal |y|⁻¹ ≠ 0} := by
    rintro _ ⟨g, -, rfl⟩
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (abs_pos.mpr (hne g)))).ne'
  rw [inter_eq_self_of_subset_right hsub]
  exact hopen.measure_ne_zero volume (hUne.image e)

private theorem pullback_isMulLeftInvariant [Group G] [IsTopologicalGroup G] (he : IsOpenEmbedding e)
    (hmul : ∀ g h : G, e (g * h) = e g * e h) (hne : ∀ g : G, e g ≠ 0) : IsMulLeftInvariant (pullback e) := by
  refine ⟨fun g => ?_⟩
  ext s hs
  have hg : Measurable (g * ·) := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hg hs, pullback_apply he, pullback_apply he]
  have himage : e '' ((g * ·) ⁻¹' s) = (e g * ·) ⁻¹' (e '' s) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g * x, hx, hmul g x⟩
    · rintro ⟨z, hz, hzy⟩
      refine ⟨g⁻¹ * z, ?_, ?_⟩
      · show g * (g⁻¹ * z) ∈ s
        rwa [mul_inv_cancel_left]
      · have h1 : e g * e (g⁻¹ * z) = e z := by rw [← hmul, mul_inv_cancel_left]
        have h2 : e g * e (g⁻¹ * z) = e g * y := by rw [h1, hzy]
        exact mul_left_cancel₀ (hne g) h2
  rw [himage, ← Measure.map_apply (measurable_const_mul (e g)) (he.measurableEmbedding.measurableSet_image' hs),
    map_mul_left_lineHaar (hne g)]

private theorem pullback_isHaarMeasure [Group G] [IsTopologicalGroup G] (he : IsOpenEmbedding e)
    (hmul : ∀ g h : G, e (g * h) = e g * e h) (hne : ∀ g : G, e g ≠ 0) : IsHaarMeasure (pullback e) := by
  haveI := pullback_isFiniteMeasureOnCompacts he hne
  haveI := pullback_isMulLeftInvariant he hmul hne
  haveI := pullback_isOpenPosMeasure he hne
  exact IsHaarMeasure.mk

private theorem map_pullback (he : IsOpenEmbedding e) (hrange : ∀ y : ℝ, y ≠ 0 → y ∈ range e) :
    Measure.map e (pullback e) = lineHaar := by
  rw [pullback, he.measurableEmbedding.map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  refine measure_mono_null ?_ lineHaar_singleton_zero
  intro y hy
  rw [mem_singleton_iff]
  by_contra h0
  exact hy (hrange y h0)

private theorem exists_map_eq_smul [Group G] [IsTopologicalGroup G] (he : IsOpenEmbedding e)
    (hmul : ∀ g h : G, e (g * h) = e g * e h) (hne : ∀ g : G, e g ≠ 0) (hrange : ∀ y : ℝ, y ≠ 0 → y ∈ range e)
    (ν : Measure G) [ν.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧ Measure.map e ν = ENNReal.ofReal κ • lineHaar := by
  haveI : LocallyCompactSpace G := he.locallyCompactSpace
  haveI : SecondCountableTopology G := he.isEmbedding.secondCountableTopology
  haveI : IsHaarMeasure (pullback e) := pullback_isHaarMeasure he hmul hne
  obtain ⟨r, hr, hν⟩ : ∃ r : NNReal, 0 < r ∧ ν = r • pullback e :=
    ⟨_, haarScalarFactor_pos_of_isHaarMeasure ν (pullback e), isMulLeftInvariant_eq_smul ν (pullback e)⟩
  refine ⟨(r : ℝ), NNReal.coe_pos.mpr hr, ?_⟩
  rw [ENNReal.ofReal_coe_nnreal, hν, Measure.map_smul, map_pullback he hrange]
  exact (Measure.coe_nnreal_smul r lineHaar).symm

end Group

end ArchUnitsHaar

end HaarScalar

namespace DirectArchZetaBound

private theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem continuous_realCoord : Continuous (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

private noncomputable def realCoordEquiv : InfiniteAdeleRing ℚ ≃+* ℝ where
  toFun := StandardKernel.realCoord
  invFun := StandardKernel.ofReal
  left_inv := StandardKernel.ofReal_realCoord
  right_inv := realCoord_ofReal
  map_mul' := map_mul StandardKernel.realCoord
  map_add' := map_add StandardKernel.realCoord

private noncomputable def unitsHomeomorph : (InfiniteAdeleRing ℚ)ˣ ≃ₜ ℝˣ where
  toEquiv := (Units.mapEquiv realCoordEquiv.toMulEquiv).toEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨continuous_realCoord.comp Units.continuous_val, continuous_realCoord.comp Units.continuous_coe_inv⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨StandardKernel.continuous_ofReal.comp Units.continuous_val,
      StandardKernel.continuous_ofReal.comp Units.continuous_coe_inv⟩

private theorem unitsHomeomorph_apply_val (z : (InfiniteAdeleRing ℚ)ˣ) :
    ((unitsHomeomorph z : ℝˣ) : ℝ) = StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) :=
  rfl

private theorem isOpenEmbedding_realCoord_units :
    IsOpenEmbedding fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) :=
  Units.isOpenEmbedding_val.comp unitsHomeomorph.isOpenEmbedding

private theorem realCoord_units_mul (z w : (InfiniteAdeleRing ℚ)ˣ) :
    StandardKernel.realCoord ((z * w : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) =
      StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) * StandardKernel.realCoord (w : InfiniteAdeleRing ℚ) := by
  rw [Units.val_mul, map_mul]

private theorem realCoord_units_ne_zero (z : (InfiniteAdeleRing ℚ)ˣ) :
    StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) ≠ 0 :=
  (z.isUnit.map StandardKernel.realCoord).ne_zero

private theorem realCoord_units_range (y : ℝ) (hy : y ≠ 0) :
    y ∈ Set.range fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) := by
  refine ⟨unitsHomeomorph.symm (Units.mk0 y hy), ?_⟩
  show ((unitsHomeomorph (unitsHomeomorph.symm (Units.mk0 y hy)) : ℝˣ) : ℝ) = y
  rw [Homeomorph.apply_symm_apply]
  rfl

private theorem exists_haarScalar [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
        ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹ :=
  ArchUnitsHaar.exists_map_eq_smul isOpenEmbedding_realCoord_units realCoord_units_mul realCoord_units_ne_zero
    realCoord_units_range ν_mul

end DirectArchZetaBound

end AssemblyHaarScalar

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.differentiableAt_Gammaℝ_add (w a : ℂ) (ha : 0 < (w + a).re) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℝ (z + a)) w := by
  have hpole : ∀ m : ℕ, (w + a) / 2 ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [Complex.add_re] at ha
    simp at hre
    linarith
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + a) / 2)) w :=
    ((((differentiableAt_id.add (differentiableAt_const a)).neg).div_const 2).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((z + a) / 2)) w :=
    (Complex.differentiableAt_Gamma _ hpole).comp w
      ((differentiableAt_id.add (differentiableAt_const a)).div_const 2)
  have h__af := h1.mul h2
  simp [Complex.Gammaℝ_def] at h__af ⊢
  exact h__af

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "signEpsilon RealArchParam signShift RealArchParam.gammaR RealArchParam.gammaC RealArchParam.archFactor RealArchParam.twist RealArchParam.dual RealArchParam.twist_twist RealArchParam.gammaC_twist RealArchParam.gammaR_twist_zero RealArchParam.discrete RealArchParam.principal LDatum LDatum.archFactor LDatum.archFactorDual CubicLambda.lambdaArch CubicInduction.IsArchZeta30ConvergentAbove CubicInduction.IsArchZeta31ConvergentAbove HeckeTate.heckeDatum CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous CubicInduction.jacquetVector3_isArchZetaConvergentAbove CubicInduction.isGL3PsiWhittakerFn_jacquetVector3 CubicInduction.jacquetVector3_scalar_mul CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar CubicInduction.heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR CubicInduction.heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq CubicInduction.isKFinite_jacquetVector3 CubicInduction.jacquetVector3_norm_archComponent3_le CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul CubicInduction.forall_pow_mul_norm_archZeta30_jacquetVector3_le CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le" namespace RealArchParam p2m_export "LanglandsTunnell.RealArchParam" "gammaR gammaC archFactor twist dual twist_twist gammaC_twist gammaR_twist_zero discrete principal" end LanglandsTunnell.RealArchParam
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.RealArchParam" in

private theorem LanglandsTunnell.RealArchParam.differentiableOn_archFactor (P : RealArchParam) (c : ℝ)
    (hR : ∀ μ ∈ P.gammaR, -μ.re ≤ c) (hC : ∀ μ ∈ P.gammaC, -μ.re ≤ c) :
    DifferentiableOn ℂ P.archFactor {w : ℂ | c < w.re} := by
  intro w hw
  have hw' : c < w.re := hw
  refine DifferentiableAt.differentiableWithinAt ?_
  have h1 := LanglandsTunnell.CubicInduction.differentiableAt_multiset_prod_Gammaℝ P.gammaR w
    (fun μ hμ => by have := hR μ hμ; simp only [Complex.add_re]; linarith)
  have h2 := LanglandsTunnell.CubicInduction.differentiableAt_multiset_prod_Gammaℂ P.gammaC w
    (fun μ hμ => by have := hC μ hμ; simp only [Complex.add_re]; linarith)
  have : P.archFactor = fun z => (P.gammaR.map fun μ => Complex.Gammaℝ (z + μ)).prod *
      (P.gammaC.map fun μ => Complex.Gammaℂ (z + μ)).prod := by
    funext z; rfl
  rw [this]
  exact h1.mul h2

p2m_open_scoped "LanglandsTunnell" in

private theorem LanglandsTunnell.signShift_re_nonneg (b : ZMod 2) : 0 ≤ (LanglandsTunnell.signShift b).re := by
  unfold LanglandsTunnell.signShift
  split_ifs <;> simp

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.RealArchParam" in

private theorem LanglandsTunnell.RealArchParam.forall_twist_neg_re_lt_quarter_of_principal (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2)
    (h₁ : u₁.re = 0) (h₂ : u₂.re = 0) (b : ZMod 2) :
    (∀ μ ∈ ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).gammaR, -μ.re < 1 / 4) ∧
      (∀ ν ∈ ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).gammaC, -ν.re < 1 / 4) := by
  refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
  · simp only [RealArchParam.twist, RealArchParam.gammaR, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hμ
    have hs₁ := LanglandsTunnell.signShift_re_nonneg (a₁ + b)
    have hs₂ := LanglandsTunnell.signShift_re_nonneg (a₂ + b)
    rcases hμ with hμ | hμ <;> rw [hμ] <;> simp only [Complex.add_re, Complex.zero_re] <;> linarith
  · simp [RealArchParam.twist, RealArchParam.gammaC] at hν

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.RealArchParam" in

private theorem LanglandsTunnell.RealArchParam.forall_twist_neg_re_lt_quarter_of_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (h : u.re = 0) (b : ZMod 2) :
    (∀ μ ∈ ((RealArchParam.discrete u k hk).twist 0 b).gammaR, -μ.re < 1 / 4) ∧
      (∀ ν ∈ ((RealArchParam.discrete u k hk).twist 0 b).gammaC, -ν.re < 1 / 4) := by
  refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
  · simp [RealArchParam.twist, RealArchParam.gammaR] at hμ
  · simp only [RealArchParam.twist, RealArchParam.gammaC, Multiset.mem_singleton] at hν
    have hk2 : ((k : ℂ) / 2).re = (k : ℝ) / 2 := by
      have e : ((k : ℂ) / 2) = (((k : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.ofReal_re]
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    rw [hν]
    simp only [Complex.add_re, add_zero]
    rw [hk2, h]
    linarith

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.RealArchParam" in

private theorem LanglandsTunnell.RealArchParam.dual_principal (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    (RealArchParam.principal u₁ a₁ u₂ a₂).dual = RealArchParam.principal (-u₁) a₁ (-u₂) a₂ := rfl

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.RealArchParam" in

private theorem LanglandsTunnell.RealArchParam.dual_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (RealArchParam.discrete u k hk).dual = RealArchParam.discrete (-u) k hk := rfl

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.RealArchParam" in

private theorem LanglandsTunnell.RealArchParam.dual_twist (P : RealArchParam) (u : ℂ) (b : ZMod 2) :
    (P.twist u b).dual = P.dual.twist (-u) b := by
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    simp only [RealArchParam.twist, RealArchParam.dual]
    congr 1 <;> ring
  | discrete u₀ k hk =>
    simp only [RealArchParam.twist, RealArchParam.dual]
    congr 1
    ring

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.RealArchParam" in

private theorem LanglandsTunnell.RealArchParam.gammaR_twist (P : RealArchParam) (t : ℂ) (b : ZMod 2) :
    (P.twist t b).gammaR = ((P.twist 0 b).gammaR).map (· + t) := by
  rw [← RealArchParam.gammaR_twist_zero, RealArchParam.twist_twist, zero_add, add_zero]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.RealArchParam" in

private theorem LanglandsTunnell.RealArchParam.gammaC_twist' (P : RealArchParam) (t : ℂ) (b : ZMod 2) :
    (P.twist t b).gammaC = ((P.twist 0 b).gammaC).map (· + t) := by
  rw [RealArchParam.gammaC_twist, RealArchParam.gammaC_twist]
  simp

namespace LanglandsTunnell.RealArchParam
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.RealArchParam" in

private theorem _root_.LanglandsTunnell.RealArchParam.archFactor_ne_zero_of_forall_re_pos (P : RealArchParam) (s : ℂ)
    (hR : ∀ μ ∈ P.gammaR, 0 < (s + μ).re) (hC : ∀ μ ∈ P.gammaC, 0 < (s + μ).re) : P.archFactor s ≠ 0 := by
  rw [LanglandsTunnell.RealArchParam.archFactor]
  refine mul_ne_zero (Multiset.prod_ne_zero ?_) (Multiset.prod_ne_zero ?_)
  · intro h
    obtain ⟨μ, hμ, h0⟩ := Multiset.mem_map.mp h
    exact Complex.Gammaℝ_ne_zero_of_re_pos (hR μ hμ) h0
  · intro h
    obtain ⟨μ, hμ, h0⟩ := Multiset.mem_map.mp h
    have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    refine (mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos (hC μ hμ))) h0
    intro hz
    rw [Complex.cpow_eq_zero_iff] at hz
    exact h2π hz.1

end LanglandsTunnell.RealArchParam
p2m_export "" "LanglandsTunnell.RealArchParam.archFactor_ne_zero_of_forall_re_pos"
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.exists_forall_pow_mul_norm_le_of_transfer
    (F Z A G w : ℂ → ℂ) (c : ℂ) (σ₁ σ₂ : ℝ) (N k : ℕ) (m C₆ T₆ CD TD : ℝ)
    (hc : c ≠ 0) (hm : 0 < m)
    (hw : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → m ≤ ‖w s‖)
    (hid : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → F s * (c * w s * G s) = Z s * A s)
    (hG : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → G s ≠ 0)
    (hA : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₆ ≤ |s.im| → ‖A s‖ ≤ C₆ * |s.im| ^ k * ‖G s‖)
    (hZ : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → TD ≤ |s.im| → |s.im| ^ (N + k) * ‖Z s‖ ≤ CD) :
    ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| → |s.im| ^ N * ‖F s‖ ≤ C := by
  refine ⟨max CD 0 * max C₆ 0 / (‖c‖ * m), max T₆ TD, fun s h₁ h₂ hT => ?_⟩
  have hT₆ : T₆ ≤ |s.im| := le_trans (le_max_left _ _) hT
  have hTD : TD ≤ |s.im| := le_trans (le_max_right _ _) hT
  have hcm : 0 < ‖c‖ * m := mul_pos (norm_pos_iff.mpr hc) hm
  have hGpos : 0 < ‖G s‖ := norm_pos_iff.mpr (hG s h₁ h₂)
  have ht : 0 ≤ |s.im| := abs_nonneg _
  have htk : 0 ≤ |s.im| ^ k := pow_nonneg ht k
  have htN : 0 ≤ |s.im| ^ N := pow_nonneg ht N
  have h1 : ‖F s‖ * (‖c‖ * ‖w s‖ * ‖G s‖) = ‖Z s‖ * ‖A s‖ := by
    have e := congrArg (fun z : ℂ => ‖z‖) (hid s h₁ h₂)
    simpa only [norm_mul] using e
  have h2 : ‖A s‖ ≤ max C₆ 0 * |s.im| ^ k * ‖G s‖ :=
    le_trans (hA s h₁ h₂ hT₆)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) htk) hGpos.le)
  have h3 : ‖F s‖ * (‖c‖ * ‖w s‖) ≤ ‖Z s‖ * (max C₆ 0 * |s.im| ^ k) := by
    have h3' : ‖F s‖ * (‖c‖ * ‖w s‖) * ‖G s‖ ≤ ‖Z s‖ * (max C₆ 0 * |s.im| ^ k) * ‖G s‖ := by
      calc ‖F s‖ * (‖c‖ * ‖w s‖) * ‖G s‖ = ‖F s‖ * (‖c‖ * ‖w s‖ * ‖G s‖) := by ring
        _ = ‖Z s‖ * ‖A s‖ := h1
        _ ≤ ‖Z s‖ * (max C₆ 0 * |s.im| ^ k * ‖G s‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖Z s‖ * (max C₆ 0 * |s.im| ^ k) * ‖G s‖ := by ring
    exact le_of_mul_le_mul_right h3' hGpos
  have h4 : ‖F s‖ * (‖c‖ * m) ≤ ‖Z s‖ * (max C₆ 0 * |s.im| ^ k) :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hw s h₁ h₂) (norm_nonneg _)) (norm_nonneg _))
      h3
  have h5 : |s.im| ^ N * ‖F s‖ * (‖c‖ * m) ≤ max CD 0 * max C₆ 0 := by
    calc |s.im| ^ N * ‖F s‖ * (‖c‖ * m) = |s.im| ^ N * (‖F s‖ * (‖c‖ * m)) := by ring
      _ ≤ |s.im| ^ N * (‖Z s‖ * (max C₆ 0 * |s.im| ^ k)) := mul_le_mul_of_nonneg_left h4 htN
      _ = |s.im| ^ (N + k) * ‖Z s‖ * max C₆ 0 := by rw [pow_add]; ring
      _ ≤ max CD 0 * max C₆ 0 :=
        mul_le_mul_of_nonneg_right (le_trans (hZ s h₁ h₂ hTD) (le_max_left _ _)) (le_max_right _ _)
  rw [le_div_iff₀ hcm]
  exact h5

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.exists_pos_forall_le_norm_cpow (x : ℝ) (hx : 0 < x) (σ₁ σ₂ : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → m ≤ ‖(x : ℂ) ^ (3 * (s - 1 / 2))‖ := by
  refine ⟨min (x ^ (3 * (σ₁ - 1 / 2))) (x ^ (3 * (σ₂ - 1 / 2))),
    lt_min (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hx _), fun s h₁ h₂ => ?_⟩
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (3 * (s - 1 / 2)).re = 3 * (s.re - 1 / 2) := by
    simp [Complex.mul_re, Complex.sub_re]
  rw [hre]
  rcases le_or_gt 1 x with h1 | h1
  · exact le_trans (min_le_left _ _) (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
  · exact le_trans (min_le_right _ _) (Real.rpow_le_rpow_of_exponent_ge hx h1.le (by linarith))

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_archZeta_package.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_archZeta_package.LanglandsTunnell.CubicInduction in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (hJ : jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S ≠ 0) :
      (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) ≠ 0 ∧ IsKFinite (jacquetVector3 D (uR w₀ h₀) (aR w₀
          h₀) (a : ℝ) psiInf S) ∧
        (Continuous (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g :
            AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖(jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
          C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
        IsGL3PsiWhittakerFn psiInf (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) ∧
        (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
          (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g)
              = ((ω (E z) : ℂˣ) : ℂ) * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) g) ∧
        (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
          ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
          ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
            (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ)
                psiInf S) (h * gInf)) (σ.comp E) 1 σ₀ ∧
              ∀ s : ℂ, σ₀ < s.re →
                archZeta30 ν_mul (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf))
                    (σ.comp E) s 1 =
                  P s *
                    (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                      (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
            (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
              ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
            (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
              |s.im| ^ N *
                ‖P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
            (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => (jacquetVector3 D (uR w₀
                h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf)))
                (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
              ∀ s : ℂ, σ₁ < (1 - s).re →
                archZetaDual31 ν_mul ν_add (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h *
                    gInf)) (σ.comp E) (1 - s) 1 =
                  (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                      fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                    ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                        fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                    ∏ w : InfinitePlace K, lambdaArch K w) *
                  (((ω (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                  (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                  P s *
                    (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                      (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) := by
  refine ⟨hJ, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    exact LanglandsTunnell.CubicInduction.isKFinite_jacquetVector3 K hdeg μ hμ uR aR uC kC huR huC ω hω E hE a
      aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS
  ·
    exact (LanglandsTunnell.CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous K hdeg μ hμ
      uR aR uC kC huR huC ω hω E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS).2
  ·
    exact LanglandsTunnell.CubicInduction.jacquetVector3_norm_archComponent3_le K hdeg μ hμ uR aR uC kC huR huC ω
      hω E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS
  ·
    exact LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_jacquetVector3 P₂ D (uR w₀ h₀) (aR w₀ h₀) a psiInf
      hpsiInf S
  ·
    exact LanglandsTunnell.CubicInduction.jacquetVector3_scalar_mul K uR aR uC kC ω hω E hE a psiInf w₀ h₀ P₂ hP₂
      D S
  ·
    intro σ hσ t e hte gInf
    have hre : ∀ (w : InfinitePlace K) (hw : w.IsReal), (uR w hw).re = 0 := fun w hw =>
      LanglandsTunnell.CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar K μ hμ.2.2 w (uR w hw) _ (huR w hw)
    have hreC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), (uC w hw).re = 0 := fun w hw =>
      LanglandsTunnell.CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar K μ hμ.2.2 w (uC w hw) _ (huC w hw)
    have hneg : ∀ u : ℂ, u.re = 0 → (-u).re = 0 := fun u hu => by rw [Complex.neg_re, hu, neg_zero]
    have hc₀ : ∀ b : ZMod 2,
        (∀ ν ∈ (P₂.twist 0 b).gammaR, -ν.re < 1 / 4) ∧ (∀ ν ∈ (P₂.twist 0 b).gammaC, -ν.re < 1 / 4) := by
      intro b
      rcases hP₂ with ⟨w₁, w₂, h₁, h₂, -, -, -, -, rfl⟩ | ⟨wC, hC, -, ⟨hk, rfl⟩ | ⟨-, rfl⟩⟩
      · exact LanglandsTunnell.RealArchParam.forall_twist_neg_re_lt_quarter_of_principal _ _ _ _ (hre w₁ h₁)
          (hre w₂ h₂) b
      · exact LanglandsTunnell.RealArchParam.forall_twist_neg_re_lt_quarter_of_discrete _ _ _ (hreC wC hC) b
      · exact LanglandsTunnell.RealArchParam.forall_twist_neg_re_lt_quarter_of_principal _ _ _ _ (hreC wC hC)
          (hreC wC hC) b
    have hc₁ : ∀ b : ZMod 2,
        (∀ ν ∈ (P₂.dual.twist 0 b).gammaR, -ν.re < 1 / 4) ∧ (∀ ν ∈ (P₂.dual.twist 0 b).gammaC, -ν.re < 1 / 4) := by
      intro b
      rcases hP₂ with ⟨w₁, w₂, h₁, h₂, -, -, -, -, rfl⟩ | ⟨wC, hC, -, ⟨hk, rfl⟩ | ⟨-, rfl⟩⟩
      · exact LanglandsTunnell.RealArchParam.forall_twist_neg_re_lt_quarter_of_principal _ _ _ _
          (hneg _ (hre w₁ h₁)) (hneg _ (hre w₂ h₂)) b
      · exact LanglandsTunnell.RealArchParam.forall_twist_neg_re_lt_quarter_of_discrete _ _ _ (hneg _ (hreC wC hC)) b
      · exact LanglandsTunnell.RealArchParam.forall_twist_neg_re_lt_quarter_of_principal _ _ _ _
          (hneg _ (hreC wC hC)) (hneg _ (hreC wC hC)) b
    obtain ⟨κ, _hκpos, hκ⟩ := DirectArchZetaBound.exists_haarScalar ν_mul
    obtain ⟨P, hPd, hPs, hPid⟩ :=
      LanglandsTunnell.CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul (uR w₀ h₀) (aR w₀ h₀)
        P₂ D S hS a psiInf hpsiInf ha (1 / 4) hc₀ κ gInf t e
    have hconv :=
      LanglandsTunnell.CubicInduction.jacquetVector3_isArchZetaConvergentAbove K hdeg μ hμ uR aR uC kC huR huC ω hω
        E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS (1 / 4) hc₀ (1 / 4) hc₁ σ hσ t e hte
        gInf
    have hΓ := fun s : ℂ =>
      LanglandsTunnell.CubicInduction.heckeDatum_archFactor_eq_archFactor_twist_mul_GammaR K μ uR aR uC kC w₀ h₀ P₂
        hP₂ t e s
    have hR : ∀ ν ∈ (P₂.twist t (e : ZMod 2)).gammaR, -ν.re ≤ max (1 / 4) (-(uR w₀ h₀).re) - t.re := by
      intro ν hν
      rw [LanglandsTunnell.RealArchParam.gammaR_twist] at hν
      obtain ⟨ν₀, hν₀, rfl⟩ := Multiset.mem_map.mp hν
      have h4 := (hc₀ (e : ZMod 2)).1 ν₀ hν₀
      have hm : (1 / 4 : ℝ) ≤ max (1 / 4) (-(uR w₀ h₀).re) := le_max_left _ _
      simp only [Complex.add_re]
      linarith
    have hC : ∀ ν ∈ (P₂.twist t (e : ZMod 2)).gammaC, -ν.re ≤ max (1 / 4) (-(uR w₀ h₀).re) - t.re := by
      intro ν hν
      rw [LanglandsTunnell.RealArchParam.gammaC_twist'] at hν
      obtain ⟨ν₀, hν₀, rfl⟩ := Multiset.mem_map.mp hν
      have h4 := (hc₀ (e : ZMod 2)).2 ν₀ hν₀
      have hm : (1 / 4 : ℝ) ≤ max (1 / 4) (-(uR w₀ h₀).re) := le_max_left _ _
      simp only [Complex.add_re]
      linarith
    have hG : DifferentiableOn ℂ
        (fun s : ℂ => Complex.Gammaℝ (s + (uR w₀ h₀ + t + LanglandsTunnell.signShift (aR w₀ h₀ + (e : ZMod 2)))))
        {s : ℂ | max (1 / 4) (-(uR w₀ h₀).re) - t.re < s.re} := by
      intro s hs
      refine (LanglandsTunnell.CubicInduction.differentiableAt_Gammaℝ_add _ _ ?_).differentiableWithinAt
      have hs' : max (1 / 4) (-(uR w₀ h₀).re) - t.re < s.re := hs
      have h0 := hre w₀ h₀
      have hsh := LanglandsTunnell.signShift_re_nonneg (aR w₀ h₀ + (e : ZMod 2))
      have hm : -(uR w₀ h₀).re ≤ max (1 / 4) (-(uR w₀ h₀).re) := le_max_right _ _
      simp only [Complex.add_re]
      linarith
    have hAF := (LanglandsTunnell.RealArchParam.differentiableOn_archFactor _ _ hR hC).mul hG
    have hg : DifferentiableOn ℂ
        (fun s : ℂ => P s * ((P₂.twist t (e : ZMod 2)).archFactor s *
          Complex.Gammaℝ (s + (uR w₀ h₀ + t + LanglandsTunnell.signShift (aR w₀ h₀ + (e : ZMod 2))))))
        {s : ℂ | max (1 / 4) (-(uR w₀ h₀).re) - t.re < s.re} := hPd.differentiableOn.mul hAF
    have key :=
      LanglandsTunnell.CubicInduction.eqOn_halfPlane_lt_re_of_eqOn_strip
        (fun s : ℂ => archZeta30 ν_mul
          (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf)) (σ.comp E) s 1)
        (fun s : ℂ => P s * ((P₂.twist t (e : ZMod 2)).archFactor s *
          Complex.Gammaℝ (s + (uR w₀ h₀ + t + LanglandsTunnell.signShift (aR w₀ h₀ + (e : ZMod 2))))))
        (max (1 / 4) (-(uR w₀ h₀).re) - t.re)
        (max (max (1 / 4) (-(uR w₀ h₀).re) - t.re) (D.zeta_abscissa - t.re))
        (max (max (1 / 4) (-(uR w₀ h₀).re) - t.re) (D.zeta_abscissa - t.re) + 1)
        (le_max_left _ _) (by linarith)
        (LanglandsTunnell.CubicInduction.differentiableOn_archZeta30_of_isArchZeta30ConvergentAbove _ _ _ _ _
          hconv.1)
        hg (by
          intro s h1' _h2'
          have h1 : max (1 / 4) (-(uR w₀ h₀).re) - t.re < s.re := lt_of_le_of_lt (le_max_left _ _) h1'
          have h2 : D.zeta_abscissa < s.re + t.re := by
            have h2' : D.zeta_abscissa - t.re < s.re := lt_of_le_of_lt (le_max_right _ _) h1'
            linarith
          have hB :=
            LanglandsTunnell.CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul K hdeg μ hμ uR aR uC kC huR huC
              ω hω E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS (1 / 4) hc₀ κ hκ σ hσ t e
              hte gInf s h1 h2
          show archZeta30 ν_mul (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf))
              (σ.comp E) s 1 = P s * ((P₂.twist t (e : ZMod 2)).archFactor s *
                Complex.Gammaℝ (s + (uR w₀ h₀ + t + LanglandsTunnell.signShift (aR w₀ h₀ + (e : ZMod 2)))))
          exact LanglandsTunnell.CubicInduction.eq_mul_mul_of_eq_mul_mul_of_mul_eq _ _ _ _ _ _ hB (hPid s h1 h2))
    have hident : ∀ s : ℂ, max (1 / 4) (-(uR w₀ h₀).re) - t.re < s.re →
        archZeta30 ν_mul (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf)) (σ.comp E)
            s 1 =
          P s *
            (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
              (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s := by
      intro s hs
      rw [hΓ s]
      exact key hs
    have hΓD := fun s : ℂ =>
      LanglandsTunnell.CubicInduction.heckeDatum_archFactorDual_eq_archFactor_dual_twist_mul_GammaR K μ uR aR uC kC
        w₀ h₀ P₂ hP₂ t e s
    haveI : MeasureTheory.SFinite ν_add := by
      rw [hν_add]
      infer_instance
    have h0 := hre w₀ h₀
    have hmR : max (1 / 4) (-(uR w₀ h₀).re) = 1 / 4 := by rw [h0, neg_zero]; exact max_eq_left (by norm_num)
    have hmD : max (1 / 4) (uR w₀ h₀).re = 1 / 4 := by rw [h0]; exact max_eq_left (by norm_num)
    have hRD : ∀ ν ∈ ((P₂.twist t (e : ZMod 2)).dual).gammaR, -ν.re ≤ max (1 / 4) (uR w₀ h₀).re + t.re := by
      intro ν hν
      rw [LanglandsTunnell.RealArchParam.dual_twist, LanglandsTunnell.RealArchParam.gammaR_twist] at hν
      obtain ⟨ν₀, hν₀, rfl⟩ := Multiset.mem_map.mp hν
      have h4 := (hc₁ (e : ZMod 2)).1 ν₀ hν₀
      have hm : (1 / 4 : ℝ) ≤ max (1 / 4) (uR w₀ h₀).re := le_max_left _ _
      simp only [Complex.add_re, Complex.neg_re]
      linarith
    have hCD : ∀ ν ∈ ((P₂.twist t (e : ZMod 2)).dual).gammaC, -ν.re ≤ max (1 / 4) (uR w₀ h₀).re + t.re := by
      intro ν hν
      rw [LanglandsTunnell.RealArchParam.dual_twist, LanglandsTunnell.RealArchParam.gammaC_twist'] at hν
      obtain ⟨ν₀, hν₀, rfl⟩ := Multiset.mem_map.mp hν
      have h4 := (hc₁ (e : ZMod 2)).2 ν₀ hν₀
      have hm : (1 / 4 : ℝ) ≤ max (1 / 4) (uR w₀ h₀).re := le_max_left _ _
      simp only [Complex.add_re, Complex.neg_re]
      linarith
    have hGD : DifferentiableOn ℂ
        (fun w : ℂ => Complex.Gammaℝ (w + (-(uR w₀ h₀ + t) + LanglandsTunnell.signShift (aR w₀ h₀ + (e : ZMod 2)))))
        {w : ℂ | max (1 / 4) (uR w₀ h₀).re + t.re < w.re} := by
      intro w hw
      refine (LanglandsTunnell.CubicInduction.differentiableAt_Gammaℝ_add _ _ ?_).differentiableWithinAt
      have hw' : max (1 / 4) (uR w₀ h₀).re + t.re < w.re := hw
      have hsh := LanglandsTunnell.signShift_re_nonneg (aR w₀ h₀ + (e : ZMod 2))
      have hm : (1 / 4 : ℝ) ≤ max (1 / 4) (uR w₀ h₀).re := le_max_left _ _
      simp only [Complex.add_re, Complex.neg_re]
      linarith
    have hAD := (LanglandsTunnell.RealArchParam.differentiableOn_archFactor _ _ hRD hCD).mul hGD
    have h1s : DifferentiableOn ℂ (fun s : ℂ => 1 - s) {s : ℂ | s.re < 1 - (max (1 / 4) (uR w₀ h₀).re + t.re)} :=
      ((differentiable_const (1 : ℂ)).sub differentiable_id).differentiableOn
    have hmaps : Set.MapsTo (fun s : ℂ => 1 - s) {s : ℂ | s.re < 1 - (max (1 / 4) (uR w₀ h₀).re + t.re)}
        {w : ℂ | max (1 / 4) (uR w₀ h₀).re + t.re < w.re} := by
      intro s hs
      have hs' : s.re < 1 - (max (1 / 4) (uR w₀ h₀).re + t.re) := hs
      show max (1 / 4) (uR w₀ h₀).re + t.re < (1 - s).re
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hcpow : Differentiable ℂ (fun s : ℂ => ((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) := fun s =>
      ((differentiableAt_id.sub_const (1 / 2 : ℂ)).const_mul (3 : ℂ)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (Rat.cast_ne_zero.mpr ha))))
    have hf : DifferentiableOn ℂ
        (fun s : ℂ => archZetaDual31 ν_mul ν_add
          (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf)) (σ.comp E) (1 - s) 1)
        {s : ℂ | s.re < 1 - (max (1 / 4) (uR w₀ h₀).re + t.re)} :=
      (LanglandsTunnell.CubicInduction.differentiableOn_archZeta31_of_isArchZeta31ConvergentAbove _ _ _ _ _ _
        hconv.2).comp h1s hmaps
    have hg : DifferentiableOn ℂ
        (fun s : ℂ =>
          (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
              fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
            ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
            ∏ w : InfinitePlace K, lambdaArch K w) *
          (((ω (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
          (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
          P s *
          (((P₂.twist t (e : ZMod 2)).dual).archFactor (1 - s) *
            Complex.Gammaℝ (1 - s + (-(uR w₀ h₀ + t) + LanglandsTunnell.signShift (aR w₀ h₀ + (e : ZMod 2))))))
        {s : ℂ | s.re < 1 - (max (1 / 4) (uR w₀ h₀).re + t.re)} :=
      ((((differentiableOn_const _).mul hcpow.differentiableOn).mul hPd.differentiableOn).mul
        (hAD.comp h1s hmaps))
    have keyD :=
      LanglandsTunnell.CubicInduction.eqOn_halfPlane_re_lt_of_eqOn_strip _ _
        (max (1 / 4) (-(uR w₀ h₀).re) - t.re) (1 - (max (1 / 4) (uR w₀ h₀).re + t.re))
        (1 - (max (1 / 4) (uR w₀ h₀).re + t.re)) (by rw [hmR, hmD]; linarith) le_rfl hf hg (by
        intro s h1 h2
        have hs2 : max (1 / 4) (uR w₀ h₀).re + t.re < (1 - s).re := by
          rw [Complex.sub_re, Complex.one_re]
          linarith
        have hN :=
          LanglandsTunnell.CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq K hdeg μ hμ uR aR uC kC
            huR huC ω hω E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS (1 / 4) hc₀
            (1 / 4) hc₁ σ hσ t e hte gInf s h1 hs2
        have hAFne : (P₂.twist t (e : ZMod 2)).archFactor s *
            Complex.Gammaℝ (s + (uR w₀ h₀ + t + LanglandsTunnell.signShift (aR w₀ h₀ + (e : ZMod 2)))) ≠ 0 := by
          refine mul_ne_zero (LanglandsTunnell.RealArchParam.archFactor_ne_zero_of_forall_re_pos _ _ ?_ ?_)
            (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
          · intro ν hν; have := hR ν hν; rw [Complex.add_re]; linarith
          · intro ν hν; have := hC ν hν; rw [Complex.add_re]; linarith
          · have hsh := LanglandsTunnell.signShift_re_nonneg (aR w₀ h₀ + (e : ZMod 2))
            have hm : -(uR w₀ h₀).re ≤ max (1 / 4) (-(uR w₀ h₀).re) := le_max_right _ _
            simp only [Complex.add_re]
            linarith
        rw [hΓ s] at hN
        rw [hident s h1, hΓ s, hΓD (1 - s)] at hN
        apply mul_right_cancel₀ hAFne
        rw [hN]
        ring)
    have hidentD : ∀ s : ℂ, s.re < 1 - (max (1 / 4) (uR w₀ h₀).re + t.re) →
        archZetaDual31 ν_mul ν_add (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf))
            (σ.comp E) (1 - s) 1 =
          (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
              fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
            ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
            ∏ w : InfinitePlace K, lambdaArch K w) *
          (((ω (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
          (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
          P s *
            (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
              (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s) := by
      intro s hs'
      rw [hΓD (1 - s)]
      exact keyD hs'
    have hRC : (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
              fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
            ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
            ∏ w : InfinitePlace K, lambdaArch K w) *
          (((ω (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
        (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _)))
      · exact Finset.prod_ne_zero_iff.mpr fun w _ => LanglandsTunnell.signEpsilon_ne_zero _
      · exact Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ Complex.I_ne_zero
      · exact Finset.prod_ne_zero_iff.mpr fun w _ => LanglandsTunnell.CubicLambda.lambdaArch_ne_zero K w
    refine ⟨P, hPd, ⟨max (1 / 4) (-(uR w₀ h₀).re) - t.re, hconv.1, hident⟩, hPs, ?_, ?_⟩
    ·
      intro σ₁ σ₂ N
      have hstar : max (1 / 4) (-(uR w₀ h₀).re) - t.re < 1 / 2 - t.re := by rw [hmR]; linarith
      have hstarD : max (1 / 4) (uR w₀ h₀).re + t.re < 1 - (1 / 2 - t.re) := by rw [hmD]; linarith
      have hright : ∀ M : ℕ, ∃ C T₀ : ℝ, ∀ s : ℂ, 1 / 2 - t.re ≤ s.re → s.re ≤ max σ₂ (1 / 2 - t.re) → T₀ ≤ |s.im| →
          |s.im| ^ M * ‖P s * (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
            (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C := by
        intro M
        obtain ⟨C, T₀, h⟩ :=
          LanglandsTunnell.CubicInduction.forall_pow_mul_norm_archZeta30_jacquetVector3_le P₂ D (uR w₀ h₀) (aR w₀ h₀)
            E hE a psiInf hpsiInf ν_mul ha S hS (1 / 4) hc₀ σ hσ t e hte gInf (1 / 2 - t.re) (max σ₂ (1 / 2 - t.re)) M
            hstar
        refine ⟨C, T₀, fun s h₁ h₂ hT => ?_⟩
        rw [← hident s (lt_of_lt_of_le hstar h₁)]
        exact h s h₁ h₂ hT
      have hleft : ∀ M : ℕ, ∃ C T₀ : ℝ, ∀ s : ℂ, min σ₁ (1 / 2 - t.re) ≤ s.re → s.re ≤ 1 / 2 - t.re → T₀ ≤ |s.im| →
          |s.im| ^ M * ‖P s * (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
            (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C := by
        intro M
        obtain ⟨C₆, T₆, k, h₆⟩ :=
          LanglandsTunnell.LDatum.exists_forall_norm_archFactor_le_pow_mul_norm_archFactorDual
            (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t) (fun w hw => aR w hw + (e : ZMod 2))
              (fun w hw => uC w hw + t) kC)
            (le_of_eq (LanglandsTunnell.HeckeTate.card_gammaRDual_heckeDatum_add_eq K μ _ _ _ _))
            (min σ₁ (1 / 2 - t.re)) (1 / 2 - t.re)
        obtain ⟨CD, TD, hD⟩ :=
          LanglandsTunnell.CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le P₂ D (uR w₀ h₀)
            (aR w₀ h₀) E hE a psiInf hpsiInf ν_add hν_add ν_mul ha S hS (1 / 4) hc₁ σ hσ t e hte gInf
            (1 - (1 / 2 - t.re)) (1 - min σ₁ (1 / 2 - t.re)) (M + k) hstarD
        obtain ⟨m, hm, hw⟩ := LanglandsTunnell.CubicInduction.exists_pos_forall_le_norm_cpow (|a| : ℝ)
          (abs_pos.mpr (Rat.cast_ne_zero.mpr ha)) (min σ₁ (1 / 2 - t.re)) (1 / 2 - t.re)
        refine LanglandsTunnell.CubicInduction.exists_forall_pow_mul_norm_le_of_transfer _
          (fun s : ℂ => archZetaDual31 ν_mul ν_add
            (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf)) (σ.comp E) (1 - s) 1)
          _ (fun s : ℂ => (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
            (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))
          (fun s : ℂ => ((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) _ _ _ M k m C₆ T₆ CD TD hRC hm hw ?_ ?_ h₆ ?_
        ·
          intro s _ h₂
          beta_reduce
          have hs' : s.re < 1 - (max (1 / 4) (uR w₀ h₀).re + t.re) := by linarith
          rw [hidentD s hs']
          ring
        ·
          intro s _ h₂
          beta_reduce
          have hs' : max (1 / 4) (uR w₀ h₀).re + t.re < 1 - s.re := by linarith
          rw [hΓD (1 - s)]
          refine mul_ne_zero (LanglandsTunnell.RealArchParam.archFactor_ne_zero_of_forall_re_pos _ _ ?_ ?_)
            (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
          · intro ν hν; have := hRD ν hν; rw [Complex.add_re, Complex.sub_re, Complex.one_re]; linarith
          · intro ν hν; have := hCD ν hν; rw [Complex.add_re, Complex.sub_re, Complex.one_re]; linarith
          · have hsh := LanglandsTunnell.signShift_re_nonneg (aR w₀ h₀ + (e : ZMod 2))
            have hm4 : (1 / 4 : ℝ) ≤ max (1 / 4) (uR w₀ h₀).re := le_max_left _ _
            simp only [Complex.add_re, Complex.neg_re, Complex.sub_re, Complex.one_re]
            linarith
        ·
          intro s h₁ h₂ hT
          have := hD (1 - s) (by rw [Complex.sub_re, Complex.one_re]; linarith)
            (by rw [Complex.sub_re, Complex.one_re]; have := min_le_left σ₁ (1 / 2 - t.re); linarith)
            (by rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]; exact hT)
          rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
          exact this
      obtain ⟨C, T₀, h⟩ :=
        LanglandsTunnell.CubicInduction.forall_exists_pow_mul_norm_le_of_strips_union _ (min σ₁ (1 / 2 - t.re))
          (1 / 2 - t.re) (max σ₂ (1 / 2 - t.re)) hleft hright N
      exact ⟨C, T₀, fun s h₁ h₂ hT => h s (le_trans (min_le_left _ _) h₁) (le_trans h₂ (le_max_left _ _)) hT⟩
    ·
      refine ⟨max (1 / 4) (uR w₀ h₀).re + t.re, hconv.2, fun s hs => hidentD s ?_⟩
      rw [Complex.sub_re, Complex.one_re] at hs
      linarith

end S_LanglandsTunnell_CubicInduction_jacquetVector3_archZeta_package
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_archZeta_package (solution)
