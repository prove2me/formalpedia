-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_esscher_grid_past_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:46:17.300647+00:00
-- url     : https://prove2.me/submissions/ca969129-ae7e-4b6e-ad8b-f3590596fd81

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_predictable_grid_past_event_mean_zero
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_weight_horizon_bound
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_martingale
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every finite predictable Esscher product grid has zero gain on an
earlier filtration event, uniformly on a fixed compact horizon. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T : NNReal) (u : ℕ → NNReal) (hu : Monotone u)
    (hT : ∀ i, u i ≤ T)
    (n : ℕ) (s : NNReal) (hs : s ≤ u 0)
    (A : Set Ω) (hA : MeasurableSet[F s] A) :
    (∫ w in A, ∑ i ∈ Finset.range n,
      Real.exp (-alpha * runningSup L (u i) w +
         L.ψ alpha * (u i : Real)) *
      (Real.exp (alpha * L.X (u (i + 1)) w -
         L.ψ alpha * (u (i + 1) : Real)) -
       Real.exp (alpha * L.X (u i) w -
         L.ψ alpha * (u i : Real))) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := L.isProbability
  let E : NNReal → Ω → Real := fun r w =>
    Real.exp (alpha * L.X r w - L.ψ alpha * (r : Real))
  let W : ℕ → Ω → Real := fun i w =>
    Real.exp (-alpha * runningSup L (u i) w +
      L.ψ alpha * (u i : Real))
  have hE : Martingale E F P := by
    simpa only [E, SpectrallyNegativeLevy.ψ, mul_comm] using
      (esscher_exp_process_martingale L alpha hAlpha)
  have hUa : Adapted F (runningSup L) :=
    (runningSup_isDividendStrategy L).2.2.2
  have hW (i : ℕ) : Measurable[F (u i)] (W i) := by
    dsimp [W]
    exact ((measurable_const.mul (hUa (u i))).add measurable_const).exp
  have hBound (i : ℕ) (w : Ω) :
      ‖W i w‖ ≤ Real.exp (|L.ψ alpha| * (T : Real)) := by
    have h := Kyprianou.Ch04.kw47_esscher_weight_horizon_bound
      L alpha hAlpha T (u i) (hT i) w
    simpa only [W, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using h
  exact Kyprianou.Ch04.kw47_predictable_grid_past_event_mean_zero
    P F E hE W u hu hW
    (Real.exp (|L.ψ alpha| * (T : Real))) hBound
    n s hs A hA
