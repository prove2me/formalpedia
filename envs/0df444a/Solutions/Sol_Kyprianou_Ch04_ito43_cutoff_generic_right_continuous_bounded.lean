-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_generic_right_continuous_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:10:16.412954+00:00
-- url     : https://prove2.me/submissions/da15e4a7-2a0f-47ef-bb3b-891483200958

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_sum_regular
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_jump_cumulative_regular
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_grid_cell_regular
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
    (T : NNReal) :
    let E : ℕ → NNReal → ℝ := fun n t =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∑' s : Set.Ioc (0 : NNReal) t, K s.1 (L s.1) (X s.1-L s.1)) -
        (∑ k ∈ Finset.range n, K (u k) (X (u k))
          (X (v (k+1))-X (v k)))
    ∀ n, (∀ t, ContinuousWithinAt (fun s => |E n s|) (Set.Ici t) t) ∧
      BddAbove (Set.range (fun t : Set.Iic T => |E n t|)) := by
  intro E n
  let u : ℕ → NNReal := fun i => T*(i:NNReal)/(n:NNReal)
  let J : NNReal → ℝ := fun t =>
    ∑' s : Ioc (0:NNReal) t, K s.1 (L s.1) (X s.1-L s.1)
  let F : ℕ → NNReal → ℝ := fun k t =>
    K (u k) (X (u k)) (X (min t (u (k+1)))-X (min t (u k)))
  obtain ⟨hj,M,hM⟩ := Kyprianou.Ch04.ito43_cutoff_jump_cumulative_regular
    X L hCad hLeft K hK ρ hρ hzero T
  have hF (k : ℕ) := Kyprianou.Ch04.ito43_cutoff_grid_cell_regular
    X L hCad hLeft K hK ρ hρ hzero T n k
  obtain ⟨hf,N,hN⟩ := Kyprianou.Ch04.ito43_cutoff_finite_sum_regular
    (Finset.range n) F T (fun k _ => (hF k).1) (fun k _ => (hF k).2)
  constructor
  · intro t
    exact ((hj t).sub (hf t)).abs
  · refine ⟨M+N,?_⟩
    rintro y ⟨t,rfl⟩
    change |J t.1 - ∑ k ∈ Finset.range n, F k t.1| ≤ M+N
    have h := abs_sub_le (J t.1) 0 (∑ k ∈ Finset.range n, F k t.1)
    simp only [sub_zero,zero_sub,abs_neg] at h
    exact h.trans (add_le_add (hM t.1 t.2) (hN t.1 t.2))
