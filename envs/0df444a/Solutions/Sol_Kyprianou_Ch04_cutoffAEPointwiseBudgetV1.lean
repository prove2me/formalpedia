-- Prove2me | solution 1 for Kyprianou.Ch04.cutoffAEPointwiseBudgetV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:01:21.430886+00:00
-- url     : https://prove2.me/submissions/4a269c5e-5436-4cf0-b304-bcf6f50ffb5d

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_integratedKernelBudgetV1
import Theorems.Thm_Kyprianou_Ch04_levyBandEnergyV1
import Theorems.Thm_Kyprianou_Ch04_cutoffPredictableIntegrandSquareBoundV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Lift the two-band pointwise square bound to a common left-limit budget. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (a b K : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (T : NNReal) (g : ℝ → ℝ → ℝ) (U V : NNReal → Ω → ℝ) (S : Ω → ℝ)
    (hG : ∀ s : ℝ, 0 ≤ s → Differentiable ℝ (g s))
    (hGbound : ∀ s x : ℝ, 0 ≤ s → |g s x| ≤ K)
    (hD : ∀ s x : ℝ, 0 ≤ s → |deriv (g s) x| ≤ K)
    (hLeft : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → t ≤ T →
      (U t ω - V t ω)^2 ≤ S ω) :
    ∀ᵐ ω ∂P, ∀ s ∈ Ioc (0 : ℝ) (T : ℝ), ∀ z : ℝ,
      (({w : ℝ | a < |w| ∧ |w| < 1}).indicator
          (fun w => w * g s (U s.toNNReal ω)) z -
        ({w : ℝ | b < |w| ∧ |w| < 1}).indicator
          (fun w => w * g s (V s.toNNReal ω)) z)^2 ≤
      K^2 * (({w : ℝ | a < |w| ∧ |w| ≤ b ∧ |w| < 1}).indicator (fun w => w^2) z +
        ({w : ℝ | b < |w| ∧ |w| < 1}).indicator (fun w => w^2) z * S ω) := by
  let A : Set ℝ := {z | a < |z| ∧ |z| ≤ b ∧ |z| < 1}
  let B : Set ℝ := {z | b < |z| ∧ |z| < 1}
  let H (s z : ℝ) (ω : Ω) :=
    ({w : ℝ | a < |w| ∧ |w| < 1}).indicator
      (fun w => w * g s (U s.toNNReal ω)) z -
    B.indicator (fun w => w * g s (V s.toNNReal ω)) z
  filter_upwards [hLeft] with ω hω
  intro s hs z
  have hspos : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs.1
  have hsT : s.toNNReal ≤ T := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal s hs.1.le]
    exact hs.2
  have h := Kyprianou.Ch04.cutoffPredictableIntegrandSquareBoundV1 (g s) K b a
    (U s.toNNReal ω) (V s.toNNReal ω) z hK hab
    (fun x => hGbound s x hs.1.le) (hG s hs.1.le) (fun x => hD s x hs.1.le)
  have hBmul : B.indicator (fun w => w^2 * (U s.toNNReal ω - V s.toNNReal ω)^2) z =
      B.indicator (fun w => w^2) z * (U s.toNNReal ω - V s.toNNReal ω)^2 := by
    by_cases hz : z ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  change (H s z ω)^2 ≤ K^2 * (A.indicator (fun w => w^2) z +
    B.indicator (fun w => w^2 * (U s.toNNReal ω - V s.toNNReal ω)^2) z) at h
  rw [hBmul] at h
  have hnn : 0 ≤ B.indicator (fun z : ℝ => z^2) z := by
    exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hω s.toNNReal hspos hsT) hnn)) (sq_nonneg _))
