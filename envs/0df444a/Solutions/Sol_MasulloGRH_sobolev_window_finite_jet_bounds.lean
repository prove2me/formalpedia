-- Prove2me | solution 1 for MasulloGRH.sobolev_window_finite_jet_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:30:02.612059+00:00
-- url     : https://prove2.me/submissions/9a848dd0-729c-4f17-8ea9-21cd1380df81

import Theorems.Thm_MasulloGRH_sobolev_window_jet_integrable_iff
import Theorems.Thm_MasulloGRH_sobolev_jet_weight_integrable_iff
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem solution (M : ℕ) (s α : ℝ) (hα : 0 ≤ α) (hs : 2 * (M : ℝ) + 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), m ≤ M → ∀ b : ℝ, |b| ≤ α →
      C⁻¹ ≤ ∫ x : ℝ, Real.exp (2 * b * x - 2 * α * |x|) *
        (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)) ∧
      (∫ x : ℝ, Real.exp (2 * b * x - 2 * α * |x|) *
        (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))) ≤ C := by
  let w : ℕ → ℝ → ℝ := fun m x => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)
  let F : ℕ → ℝ → ℝ → ℝ := fun m b x => Real.exp (2 * b * x - 2 * α * |x|) * w m x
  have hs1 : 1 < s := by have := Nat.cast_nonneg (α := ℝ) M; linarith
  have hwpos (m : ℕ) (x : ℝ) : 0 ≤ w m x := by
    dsimp [w]
    apply div_nonneg
    · rw [pow_mul]; positivity
    · positivity
  have hw (m : ℕ) (hm : m ≤ M) : Integrable (w m) := by
    apply (MasulloGRH.sobolev_jet_weight_integrable_iff m s hs1).2
    have : (m : ℝ) ≤ M := by exact_mod_cast hm
    linarith
  have hF (m : ℕ) (hm : m ≤ M) (b : ℝ) (hb : |b| ≤ α) : Integrable (F m b) := by
    apply (MasulloGRH.sobolev_window_jet_integrable_iff m s α b hs1 hb).2
    right
    have : (m : ℝ) ≤ M := by exact_mod_cast hm
    linarith
  have hpos (m : ℕ) (b x : ℝ) : 0 ≤ F m b x :=
    mul_nonneg (Real.exp_pos _).le (hwpos m x)
  let U : ℝ := ∫ x, w 0 x + w M x
  let L : ℝ := Real.exp (-8 * α) / (5 : ℝ) ^ (s / 2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hupper (m : ℕ) (hm : m ≤ M) (b : ℝ) (hb : |b| ≤ α) : (∫ x, F m b x) ≤ U := by
    apply integral_mono (hF m hm b hb) ((hw 0 (Nat.zero_le _)).add (hw M le_rfl))
    intro x
    have hbx : b * x ≤ |b| * |x| := by simpa [abs_mul] using le_abs_self (b * x)
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have := mul_le_mul_of_nonneg_right hb (abs_nonneg x)
      nlinarith
    have hpow : x ^ (2 * m) ≤ 1 + x ^ (2 * M) := by
      simp only [pow_mul]
      by_cases hx : x ^ 2 ≤ 1
      · have hp : (x ^ 2) ^ m ≤ 1 := pow_le_one₀ (sq_nonneg x) hx
        have hq := pow_nonneg (sq_nonneg x) M
        linarith
      · have hp := pow_le_pow_right₀ (le_of_not_ge hx) hm
        linarith
    calc
      F m b x ≤ w m x := mul_le_of_le_one_left (hwpos m x) hexp
      _ ≤ w 0 x + w M x := by
        dsimp [w]
        simpa [add_div] using div_le_div_of_nonneg_right hpow
          (Real.rpow_nonneg (by positivity : 0 ≤ 1 + x ^ 2) (s / 2))
  have hlower (m : ℕ) (hm : m ≤ M) (b : ℝ) (hb : |b| ≤ α) : L ≤ ∫ x, F m b x := by
    have hpoint (x : ℝ) (hx : x ∈ Icc (1 : ℝ) 2) : L ≤ F m b x := by
      have hx0 : 0 < x := by linarith [hx.1]
      have hb0 : -α ≤ b := (abs_le.mp hb).1
      have hexp : Real.exp (-8 * α) ≤ Real.exp (2 * b * x - 2 * α * |x|) := by
        apply Real.exp_le_exp.mpr
        rw [abs_of_pos hx0]
        have := mul_le_mul_of_nonneg_right hb0 hx0.le
        nlinarith [hx.2]
      have hnum : (1 : ℝ) ≤ x ^ (2 * m) := one_le_pow₀ hx.1
      have hden : (1 + x ^ 2) ^ (s / 2) ≤ (5 : ℝ) ^ (s / 2) := by
        apply Real.rpow_le_rpow (by positivity) _ (by linarith)
        nlinarith [hx.2]
      have hratio : 1 / (5 : ℝ) ^ (s / 2) ≤ w m x :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      dsimp [L, F]
      rw [div_eq_mul_one_div]
      exact mul_le_mul hexp hratio (by positivity) (Real.exp_pos _).le
    have hh := setIntegral_mono_on
      (integrableOn_const (s := Icc (1 : ℝ) 2) (by simp))
      (hF m hm b hb).integrableOn measurableSet_Icc hpoint
    have hconst : (∫ _x in Icc (1 : ℝ) 2, L) = L := by norm_num
    rw [hconst] at hh
    exact hh.trans (setIntegral_le_integral (hF m hm b hb)
      (Filter.Eventually.of_forall (hpos m b)))
  let C : ℝ := max L⁻¹ (max U 1)
  have hC1 : 1 ≤ C := (le_max_right U 1).trans (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  refine ⟨C, hC, ?_⟩
  intro m hm b hb
  constructor
  · have hLC : C⁻¹ ≤ L := by
      have := one_div_le_one_div_of_le (inv_pos.mpr hL) (le_max_left L⁻¹ (max U 1))
      simpa only [one_div, inv_inv] using this
    exact hLC.trans (hlower m hm b hb)
  · exact (hupper m hm b hb).trans ((le_max_left U 1).trans (le_max_right _ _))
