-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_selected_cell_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:52:06.09085+00:00
-- url     : https://prove2.me/submissions/0d422077-e450-4be1-b32c-f93a1a384f61

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_selected_before
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_selected_after
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (X L : NNReal → ℝ)
    (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (K : NNReal → ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ s x z, |z| ≤ ρ → K s x z = 0)
    (T : NNReal)
    (s : NNReal) (hs : 0 < s) (hsT : s ≤ T) (j : ℕ → ℕ)
    (hj : ∀ᶠ n : ℕ in atTop,
      j n < n ∧ T * (j n : NNReal) / (n : NNReal) < s ∧
      s ≤ T * ((j n+1 : ℕ) : NNReal) / (n : NNReal)) :
    let u : ℕ → ℕ → NNReal := fun n k => T * (k : NNReal) / (n : NNReal)
    let C : ℕ → NNReal → ℕ → ℝ := fun n t k =>
      K (u n k) (X (u n k))
        (X (min t (u n (k+1))) - X (min t (u n k)))
    let A : NNReal → NNReal → ℝ := fun t s =>
      if s ≤ t then K s (L s) (X s-L s) else 0
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t ≤ T, |C n t (j n) - A t s| < ε := by
  intro u C A e he
  have hb := Kyprianou.Ch04.ito43_cutoff_selected_before
    X L hCad hLeft K hK ρ hρ hzero T s hs hsT j hj
  have ha := Kyprianou.Ch04.ito43_cutoff_selected_after
    X L hCad hLeft K hK ρ hρ hzero T s hs hsT j hj e he
  filter_upwards [hb,ha] with n hn hm
  intro t ht
  by_cases hst : s ≤ t
  · simpa only [A,if_pos hst] using hm t hst
  · have hz : C n t (j n) = 0 := hn t (lt_of_not_ge hst)
    have ha0 : A t s = 0 := if_neg hst
    rw [ha0,hz,sub_zero,abs_zero]
    exact he
