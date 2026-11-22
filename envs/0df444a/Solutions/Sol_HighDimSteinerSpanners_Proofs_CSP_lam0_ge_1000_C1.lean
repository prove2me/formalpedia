-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.lam0_ge_1000_C1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:56.382934+00:00
-- url     : https://prove2.me/submissions/bc4ff7e5-a36d-48db-adb2-4d0bbba85214

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Definitions
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution (C₁ : ℕ) (hC₁ : 3 ≤ C₁) :
    2 ≤ Nat.clog 2 C₁ ∧ 1000 * C₁ ≤ cspLam0 C₁ ∧
    (cspL C₁ : ℝ) ≤ (2000000 : ℝ) * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
  have hclog_ge2 : 2 ≤ Nat.clog 2 C₁ := by
    by_contra hlt
    have hle1 : Nat.clog 2 C₁ ≤ 1 := by omega
    have hC_le : C₁ ≤ 2 ^ 1 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp hle1
    omega
  have hlam_ge : 1000 * C₁ ≤ cspLam0 C₁ := by
    unfold cspLam0
    have h10 : 10 ≤ 2 * Nat.clog 2 C₁ + 6 := by omega
    nlinarith
  refine ⟨hclog_ge2, hlam_ge, ?_⟩
  set t := Nat.clog 2 C₁
  have ht_pos : 1 ≤ t := by omega
  have hpow_lt : 2 ^ (t - 1) < C₁ := by
    by_contra hge
    push Not at hge
    have hle : Nat.clog 2 C₁ ≤ t - 1 :=
      (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hge
    omega
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogb_mono : ∀ x y : ℝ, 0 < x → x ≤ y → Real.logb 2 x ≤ Real.logb 2 y := by
    intro x y hx hxy
    unfold Real.logb
    exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (le_of_lt hlog2_pos)
  have hlogb_pow : ∀ k : ℕ, Real.logb 2 ((2 : ℝ) ^ k) = (k : ℝ) := by
    intro k
    unfold Real.logb
    rw [Real.log_pow, mul_div_cancel_right₀ _ (ne_of_gt hlog2_pos)]
  have hC1_real_ge3 : (3 : ℝ) ≤ (C₁ : ℝ) := by exact_mod_cast hC₁
  have hlog_ge1 : 1 ≤ Real.logb 2 (C₁ : ℝ) := by
    have h := hlogb_mono 2 (C₁ : ℝ) (by norm_num) (by linarith)
    simpa [hlogb_pow 1] using h
  have ht1_le : ((t - 1 : ℕ) : ℝ) ≤ Real.logb 2 (C₁ : ℝ) := by
    have hle_real : ((2 : ℝ) ^ (t - 1)) ≤ (C₁ : ℝ) := by
      exact_mod_cast (le_of_lt hpow_lt)
    have h := hlogb_mono ((2 : ℝ) ^ (t - 1)) (C₁ : ℝ) (by positivity) hle_real
    rwa [hlogb_pow (t - 1)] at h
  have ht_le : (t : ℝ) ≤ 2 * Real.logb 2 (C₁ : ℝ) := by
    rw [Nat.cast_sub ht_pos, Nat.cast_one] at ht1_le
    linarith
  have h2t6_le : 2 * (t : ℝ) + 6 ≤ 10 * Real.logb 2 (C₁ : ℝ) := by linarith
  have hlam_real : (cspLam0 C₁ : ℝ) ≤ 1000 * (C₁ : ℝ) * Real.logb 2 (C₁ : ℝ) := by
    have heq : (cspLam0 C₁ : ℝ) = 100 * (C₁ : ℝ) * (2 * (t : ℝ) + 6) := by
      dsimp [cspLam0, t]
      push_cast
      ring
    rw [heq]
    have h100C : 0 ≤ 100 * (C₁ : ℝ) := by positivity
    have hm := mul_le_mul_of_nonneg_left h2t6_le h100C
    linarith
  have hL_eq : (cspL C₁ : ℝ) = 1600 * (C₁ : ℝ) ^ 2 * (cspLam0 C₁ : ℝ) + 20 := by
    unfold cspL cspInvEta0
    push_cast
    ring
  have hC3_ge27 : (27 : ℝ) ≤ (C₁ : ℝ) ^ 3 := by nlinarith
  have hC3log_ge27 : (27 : ℝ) ≤ (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
    nlinarith
  have hm_L : 1600 * (C₁ : ℝ) ^ 2 * (cspLam0 C₁ : ℝ) ≤
      1600000 * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlam_real (by positivity : (0 : ℝ) ≤ 1600 * (C₁ : ℝ) ^ 2)
    linarith [hm,
      show 1600 * (C₁ : ℝ) ^ 2 * (1000 * (C₁ : ℝ) * Real.logb 2 (C₁ : ℝ)) =
        1600000 * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) by ring]
  linarith
end HighDimSteinerSpanners.Proofs.CSP
