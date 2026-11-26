-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_jump_cumulative_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:13:08.961053+00:00
-- url     : https://prove2.me/submissions/a6d2333b-eed6-4444-9b3a-4707c7544233

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_large_support
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_series_reindex
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_sum_regular
import Theorems.Thm_Kyprianou_Ch04_exercise41SingleVisitStepCadlagV1
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
    let J : NNReal → ℝ := fun t =>
      ∑' s : Ioc (0:NNReal) t, K s.1 (L s.1) (X s.1-L s.1)
    (∀ t, ContinuousWithinAt J (Ici t) t) ∧
      ∃ M : ℝ, ∀ t ≤ T, |J t| ≤ M := by
  intro J
  classical
  let G : NNReal → ℝ := fun s => K s (L s) (X s-L s)
  have hrep (H : NNReal) : ∃ S : Finset NNReal,
      ∀ t ≤ H, J t = ∑ s ∈ S, if s ≤ t then G s else 0 := by
    let Q : Set NNReal := {s | 0 < s ∧ s ≤ H ∧ ρ ≤ |X s-L s|}
    have hf : Q.Finite := Kyprianou.Ch04.ito43_cutoff_finite_large_support X L hCad hLeft H ρ hρ
    let S := hf.toFinset
    have hS (s : NNReal) : s ∈ S ↔ 0 < s ∧ s ≤ H ∧ ρ ≤ |X s-L s| := by simp [S,Q]
    refine ⟨S,Kyprianou.Ch04.ito43_cutoff_finite_series_reindex G H S ?_ ?_⟩
    · intro s hs
      exact ⟨((hS s).mp hs).1,((hS s).mp hs).2.1⟩
    · intro s hs hst hn
      exact hzero _ _ _ (le_of_not_ge (fun h => hn ((hS s).mpr ⟨hs,hst,h⟩)))
  have hreg (S : Finset NNReal) (H : NNReal) :=
    Kyprianou.Ch04.ito43_cutoff_finite_sum_regular S
      (fun s u => if s ≤ u then G s else 0) H
      (fun s _ t => by
        have hc := (Kyprianou.Ch04.exercise41SingleVisitStepCadlagV1 s).1 t
        simpa only [ite_mul,one_mul,zero_mul] using hc.mul_const (G s))
      (fun s _ => ⟨|G s|,fun t ht => by split_ifs <;> simp⟩)
  constructor
  · intro t
    obtain ⟨S,hS⟩ := hrep (t+1)
    have hle : t < t+1 := lt_add_of_pos_right t (by norm_num)
    have hEq : J =ᶠ[nhdsWithin t (Ici t)]
        (fun u => ∑ s ∈ S, if s ≤ u then G s else 0) := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hle)] with u hu
      exact hS u hu.le
    exact ((hreg S (t+1)).1 t).congr_of_eventuallyEq hEq (hS t hle.le)
  · obtain ⟨S,hS⟩ := hrep T
    obtain ⟨M,hM⟩ := (hreg S T).2
    exact ⟨M,fun t ht => by rw [hS t ht]; exact hM t ht⟩
