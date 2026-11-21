-- Prove2me | solution 1 for MasulloGRH.sobolev_jet_gap_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:18:52.367043+00:00
-- url     : https://prove2.me/submissions/351916de-7416-4836-8774-a374fc587013

import Theorems.Thm_MasulloGRH_sobolev_jet_weight_integrable_iff
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

private theorem phase_norm (a : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I)‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re]

private theorem phase_diff (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ =
      ‖Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1‖ := by
  have h : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) *
        Complex.exp ((b : ℂ) * Complex.I) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, phase_norm, mul_one]

theorem solution (m : ℕ) (s : ℝ)
    (hs : 2 * (m : ℝ) + 1 < s) (a b : ℕ → ℝ)
    (hab : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : ℝ,
      ‖Complex.exp (((a n * x : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((b n * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 *
      (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))) atTop (𝓝 0) := by
  let w : ℝ → ℝ := fun x => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)
  let F : ℝ → ℝ → ℝ := fun t x =>
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2 * w x
  have hs1 : 1 < s := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hw : Integrable w :=
    (MasulloGRH.sobolev_jet_weight_integrable_iff m s hs1).2 hs
  have hwpos (x : ℝ) : 0 ≤ w x := by
    dsimp [w]
    exact div_nonneg (Even.pow_nonneg (⟨m, by omega⟩ : Even (2 * m)) x)
      (Real.rpow_nonneg (by positivity) _)
  have hwc : Continuous w := by
    apply Continuous.div (by fun_prop)
    · apply Continuous.rpow_const (by fun_prop)
      intro x
      exact Or.inl (ne_of_gt (by positivity : 0 < 1 + x ^ 2))
    · intro x
      exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  have hc : Continuous (fun t => ∫ x, F t x) := by
    apply continuous_of_dominated (bound := fun x => 4 * w x)
    · intro t
      exact ((by fun_prop : Continuous (fun x : ℝ =>
        ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2)).mul hwc).aestronglyMeasurable
    · intro t
      apply Filter.Eventually.of_forall
      intro x
      have hp : ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
        calc
          _ ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [phase_norm, norm_one]; norm_num
      have hp2 : ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2 ≤ 4 := by
        nlinarith [norm_nonneg (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1)]
      dsimp [F]
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hwpos x))]
      exact mul_le_mul_of_nonneg_right hp2 (hwpos x)
    · exact hw.const_mul 4
    · apply Filter.Eventually.of_forall
      intro x
      dsimp [F]
      fun_prop
  have hzero : (∫ x, F 0 x) = 0 := by simp [F]
  have h := hc.continuousAt.tendsto.comp hab
  rw [hzero] at h
  convert h using 1
  funext n
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp [F, w]
  rw [phase_diff, ← sub_mul]
