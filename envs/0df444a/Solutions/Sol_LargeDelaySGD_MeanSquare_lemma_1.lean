-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:48:27.866482+00:00
-- url     : https://prove2.me/submissions/748cb7dd-ce1e-4d00-afd6-bf3837c3b838

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model
import Theorems.Thm_LargeDelaySGD_MeanSquare_eq_B5
import Theorems.Thm_LargeDelaySGD_MeanSquare_delay_sum_bounded
import Theorems.Thm_LargeDelaySGD_MeanSquare_delay_sum_sublinear
import Theorems.Thm_LargeDelaySGD_MeanSquare_delay_sum_linear
import Theorems.Thm_LargeDelaySGD_MeanSquare_delay_sum_polynomial

open MeasureTheory ProbabilityTheory LargeDelaySGD.MeanSquare

theorem solution {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (α : ℕ → ℝ) (s : ℕ → ℕ) (hA2 : Assumption2 α s)
    (hinf : BddBelow (Set.range (objective F μ)))
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X) :
    (∀ n, Integrable (fun a => ‖gradient (objective F μ) (X n a)‖ ^ 2) P) ∧
      Summable (fun n => α (n + 1) * ∫ a, ‖gradient (objective F μ) (X n a)‖ ^ 2 ∂P) := by
  obtain ⟨hpos, hs, hreg⟩ := hA2
  -- summability of the step-size terms in every regime
  have hsums : Summable (fun n => α (n + 1) ^ 2) ∧ Summable (delaySum α s) := by
    rcases hreg with h | h | h | h
    · exact delay_sum_bounded α s hs hpos h
    · exact ⟨(delay_sum_sublinear α s hs hpos h).1, (delay_sum_sublinear α s hs hpos h).2.2⟩
    · exact ⟨(delay_sum_linear α s hs hpos h).1, (delay_sum_linear α s hs hpos h).2.2⟩
    · exact ⟨(delay_sum_polynomial α s hs hpos h).1, (delay_sum_polynomial α s hs hpos h).2.2⟩
  -- B ≥ 0
  have hB : 0 ≤ B := le_trans (integral_nonneg (fun ξ => by positivity)) (hA1.second_moment 0)
  -- a first-moment bound: ‖g‖ ≤ (1 + ‖g‖²)/2
  have hBbar : ∀ x, ∫ ξ, ‖stochGrad F x ξ‖ ∂μ ≤ (1 + B) / 2 := by
    intro x
    have h2 : Integrable (fun ξ => ‖stochGrad F x ξ‖ ^ 2) μ :=
      (hA1.memLp x).integrable_norm_pow (by norm_num)
    have h1 : Integrable (fun ξ => ‖stochGrad F x ξ‖) μ :=
      ((hA1.memLp x).integrable (by norm_num)).norm
    have hle : ∫ ξ, ‖stochGrad F x ξ‖ ∂μ ≤ ∫ ξ, (1 + ‖stochGrad F x ξ‖ ^ 2) / 2 ∂μ := by
      apply integral_mono h1 ((integrable_const 1).add h2 |>.div_const 2)
      intro ξ
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (‖stochGrad F x ξ‖ - 1)]
    have heq : ∫ ξ, (1 + ‖stochGrad F x ξ‖ ^ 2) / 2 ∂μ
        = (1 + ∫ ξ, ‖stochGrad F x ξ‖ ^ 2 ∂μ) / 2 := by
      rw [integral_div, integral_add (integrable_const 1) h2]
      simp
    linarith [hA1.second_moment x]
  set Bbar : ℝ := (1 + B) / 2 with hBbar_def
  have hB5 := eq_B5 μ P F B L hA1 α s hs hpos ω hω x₀ X hX Bbar hBbar
  refine ⟨fun n => (hB5 n).2.1, ?_⟩
  obtain ⟨m, hm⟩ := hinf
  set e : ℕ → ℝ := fun n => ∫ a, objective F μ (X n a) ∂P with he
  set g : ℕ → ℝ := fun n => ∫ a, ‖gradient (objective F μ) (X n a)‖ ^ 2 ∂P with hg
  set c : ℕ → ℝ := fun n => (L * Bbar * Real.sqrt B) * delaySum α s n
    + (L * Real.sqrt B + 4 * L * B) * α (n + 1) ^ 2 with hc
  have hcs : Summable c :=
    (hsums.2.mul_left _).add (hsums.1.mul_left _)
  have hBbar0 : 0 ≤ Bbar := by rw [hBbar_def]; linarith
  have hds0 : ∀ n, 0 ≤ delaySum α s n := by
    intro n
    unfold delaySum
    exact mul_nonneg (hpos _).le (Finset.sum_nonneg (fun r _ => (hpos _).le))
  have hc0 : ∀ n, 0 ≤ c n := by
    intro n
    simp only [hc]
    have : (0 : ℝ) ≤ L := L.2
    have := Real.sqrt_nonneg B
    have := hds0 n
    positivity
  have hstep : ∀ n, α (n + 1) * g n ≤ e n - e (n + 1) + c n := by
    intro n
    have h := (hB5 n).2.2
    have hdl : delaySum α s n = α (n + 1) * ∑ r ∈ Finset.Ico (s n) n, α (r + 1) := rfl
    simp only [hc, he, hg, hdl] at h ⊢
    nlinarith [h]
  have he_lb : ∀ n, m ≤ e n := by
    intro n
    have hint := (hB5 n).1
    have : ∫ _a, m ∂P ≤ ∫ a, objective F μ (X n a) ∂P :=
      integral_mono (integrable_const m) hint (fun a => hm ⟨X n a, rfl⟩)
    simpa using this
  have hg0 : ∀ n, 0 ≤ α (n + 1) * g n := fun n =>
    mul_nonneg (hpos _).le (integral_nonneg (fun a => by positivity))
  apply summable_of_sum_range_le hg0 (c := e 0 - m + ∑' n, c n)
  intro N
  have htel : ∑ n ∈ Finset.range N, α (n + 1) * g n
      ≤ ∑ n ∈ Finset.range N, (e n - e (n + 1) + c n) := Finset.sum_le_sum (fun n _ => hstep n)
  rw [Finset.sum_add_distrib, Finset.sum_range_sub'] at htel
  have := hcs.sum_le_tsum (Finset.range N) (fun n _ => hc0 n)
  linarith [he_lb N]
