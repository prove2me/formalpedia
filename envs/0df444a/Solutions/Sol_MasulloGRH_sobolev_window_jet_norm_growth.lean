-- Prove2me | solution 1 for MasulloGRH.sobolev_window_jet_norm_growth
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:25:20.84908+00:00
-- url     : https://prove2.me/submissions/6c48e49f-c55c-4bb8-a449-5cfeb18db3a7

import Theorems.Thm_MasulloGRH_sobolev_window_jet_integrable_iff
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem solution (α s : ℝ) (hα : 0 < α) (hs : 1 < s) :
    Tendsto (fun m : ℕ => ∫ x : ℝ, Real.exp (-2 * α * |x|) *
      (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))) atTop atTop := by
  let F : ℕ → ℝ → ℝ := fun m x => Real.exp (-2 * α * |x|) *
    (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))
  let K : ℝ := Real.exp (-6 * α) / (10 : ℝ) ^ (s / 2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hF (m : ℕ) : Integrable (F m) := by
    have h := (MasulloGRH.sobolev_window_jet_integrable_iff m s α 0 hs
      (by simpa using hα.le)).2 (Or.inl (by simpa using hα))
    simpa [F] using h
  have hpos (m : ℕ) (x : ℝ) : 0 ≤ F m x := by
    dsimp [F]
    apply mul_nonneg (Real.exp_pos _).le
    apply div_nonneg
    · rw [pow_mul]; positivity
    · positivity
  have hbound (m : ℕ) : (4 : ℝ) ^ m * K ≤ ∫ x, F m x := by
    have hpoint (x : ℝ) (hx : x ∈ Icc (2 : ℝ) 3) : (4 : ℝ) ^ m * K ≤ F m x := by
      have hx0 : 0 < x := by linarith [hx.1]
      have hexp : Real.exp (-6 * α) ≤ Real.exp (-2 * α * |x|) := by
        apply Real.exp_le_exp.mpr
        rw [abs_of_pos hx0]
        nlinarith [hx.2]
      have hnum : (4 : ℝ) ^ m ≤ x ^ (2 * m) := by
        rw [pow_mul]
        exact pow_le_pow_left₀ (by norm_num) (by nlinarith [hx.1]) _
      have hden : (1 + x ^ 2) ^ (s / 2) ≤ (10 : ℝ) ^ (s / 2) := by
        apply Real.rpow_le_rpow (by positivity) _ (by linarith)
        nlinarith [hx.2]
      have hratio : (4 : ℝ) ^ m / (10 : ℝ) ^ (s / 2) ≤
          x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2) := by
        exact div_le_div₀ (by positivity) hnum (by positivity) hden
      dsimp [K, F]
      calc
        (4 : ℝ) ^ m * (Real.exp (-6 * α) / 10 ^ (s / 2)) =
            Real.exp (-6 * α) * ((4 : ℝ) ^ m / 10 ^ (s / 2)) := by ring
        _ ≤ _ := mul_le_mul hexp hratio (by positivity) (Real.exp_pos _).le
    have hm := setIntegral_mono_on
      (integrableOn_const (s := Icc (2 : ℝ) 3) (by simp))
      (hF m).integrableOn measurableSet_Icc hpoint
    have hconst : (∫ _x in Icc (2 : ℝ) 3, (4 : ℝ) ^ m * K) = (4 : ℝ) ^ m * K := by
      norm_num
    rw [hconst] at hm
    exact hm.trans (setIntegral_le_integral (hF m) (Filter.Eventually.of_forall (hpos m)))
  have hg : Tendsto (fun m : ℕ => (4 : ℝ) ^ m * K) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).atTop_mul_const hK
  exact tendsto_atTop_mono hbound hg
