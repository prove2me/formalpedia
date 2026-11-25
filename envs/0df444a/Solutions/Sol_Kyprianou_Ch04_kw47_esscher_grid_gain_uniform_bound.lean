-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_esscher_grid_gain_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:10:27.723839+00:00
-- url     : https://prove2.me/submissions/b8ff2476-8973-495c-a7e5-b2a462f3aace

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_E_grid_horizon_bound
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_weight_horizon_bound
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_H_grid_variation
import Theorems.Thm_Kyprianou_Ch04_kw47_grid_gain_uniform_bound
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The exact Esscher product grid is uniformly bounded on every
finite horizon by one exponential running-maximum envelope. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T : NNReal) (u : Nat → NNReal) (hu : Monotone u)
    (hT : ∀ i, u i ≤ T) (n : Nat) (w : Ω) :
    |∑ i ∈ Finset.range n,
      Real.exp (-alpha * runningSup L (u i) w +
         L.ψ alpha * (u i : Real)) *
      (Real.exp (alpha * L.X (u (i+1)) w -
         L.ψ alpha * (u (i+1) : Real)) -
       Real.exp (alpha * L.X (u i) w -
         L.ψ alpha * (u i : Real)))| ≤
      4 * Real.exp (alpha * runningSup L T w +
           |L.ψ alpha| * (T : Real)) *
          Real.exp (|L.ψ alpha| * (T : Real)) := by
  let E : Nat → Real := fun i =>
    Real.exp (alpha * L.X (u i) w - L.ψ alpha * (u i : Real))
  let H : Nat → Real := fun i =>
    Real.exp (-alpha * runningSup L (u i) w +
      L.ψ alpha * (u i : Real))
  let S : Real := Real.exp (alpha * runningSup L T w +
    |L.ψ alpha| * (T : Real))
  let C : Real := Real.exp (|L.ψ alpha| * (T : Real))
  have hE (i : Nat) : |E i| ≤ S := by
    exact Kyprianou.Ch04.kw47_esscher_E_grid_horizon_bound
      L alpha hAlpha T (u i) (hT i) w
  have hH (i : Nat) : |H i| ≤ C := by
    have h := Kyprianou.Ch04.kw47_esscher_weight_horizon_bound
      L alpha hAlpha T (u i) (hT i) w
    simpa only [H, C, abs_of_pos (Real.exp_pos _)] using h
  have hVarH : (∑ i ∈ Finset.range n,
      |H (i+1)-H i|) ≤ 2*C := by
    exact Kyprianou.Ch04.kw47_esscher_H_grid_variation
      L alpha hAlpha T u hu hT n w
  have hG := Kyprianou.Ch04.kw47_grid_gain_uniform_bound
    E H n S C (Real.exp_nonneg _) (Real.exp_nonneg _)
      hE hH hVarH
  simpa only [E,H,S,C] using hG
