-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_finite_locator_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:06:56.581903+00:00
-- url     : https://prove2.me/submissions/dc8c6787-492c-444e-87a9-4c46629639a5

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_right_closed_grid_locators_eventually_injective
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (T : NNReal) (S : Finset NNReal)
    (hS : ∀ s ∈ S, 0 < s ∧ s ≤ T) :
    ∃ j : NNReal → ℕ → ℕ,
      (∀ᶠ n : ℕ in atTop, ∀ s ∈ S,
        j s n < n ∧ T*(j s n : NNReal)/(n:NNReal) < s ∧
        s ≤ T*((j s n+1 : ℕ):NNReal)/(n:NNReal)) ∧
      (∀ᶠ n : ℕ in atTop, Set.InjOn (fun s => j s n) (S : Set NNReal)) := by
  classical
  have hloc (s : S) := AvramDividend.Classical.avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
    T s.1 ((hS s.1 s.2).1.trans_le (hS s.1 s.2).2)
    (hS s.1 s.2).1 (hS s.1 s.2).2
  choose i hi hl hr using hloc
  let j0 : NNReal → ℕ → ℕ := fun s n => if h : s ∈ S then i ⟨s,h⟩ n else 0
  have hj0 (s : NNReal) (hs : s ∈ S) (n : ℕ) : j0 s n = i ⟨s,hs⟩ n := by
    simp [j0,hs]
  have hjR (s : NNReal) (hs : s ∈ S) :
      Tendsto (fun n : ℕ => ((j0 s n+1:ℕ):NNReal) *
        (T/((n:NNReal)+1))) atTop (nhds s) := by
    simpa only [hj0 s hs] using (hr ⟨s,hs⟩).mono_right nhdsWithin_le_nhds
  have hInj := AvramDividend.Classical.avram_p2_h_cadlag_finite_right_closed_grid_locators_eventually_injective
    S (fun n s => j0 s n) T hjR
  let j : NNReal → ℕ → ℕ := fun s n => j0 s (n-1)
  refine ⟨j,?_,?_⟩
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    intro s hs
    have hn' : n-1+1 = n := Nat.sub_add_cancel hn
    have hnR : ((n-1:ℕ):NNReal)+1 = (n:NNReal) := by exact_mod_cast hn'
    have hh := hi ⟨s,hs⟩ (n-1)
    change j0 s (n-1) < n ∧ T*(j0 s (n-1):NNReal)/(n:NNReal) < s ∧
      s ≤ T*((j0 s (n-1)+1:ℕ):NNReal)/(n:NNReal)
    rw [hj0 s hs]
    rw [hnR] at hh
    have heq (r : NNReal) : r*(T/(n:NNReal)) = T*r/(n:NNReal) := by ring
    simp only [heq] at hh
    exact ⟨by omega,hh.2.1,hh.2.2⟩
  · obtain ⟨N,hN⟩ := eventually_atTop.mp hInj
    filter_upwards [eventually_ge_atTop (N+1)] with n hn
    exact hN (n-1) (by omega)
