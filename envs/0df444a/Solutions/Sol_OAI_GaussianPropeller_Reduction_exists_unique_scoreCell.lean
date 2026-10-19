-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.exists_unique_scoreCell
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:08:40.577844+00:00
-- url     : https://prove2.me/submissions/8f6e6ce8-9e32-4ca8-9872-24e259784928

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]


theorem solution (v : Fin k → Space d) (x : Space d) :
    ∃! i, x ∈ scoreCell v i := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ⟪v j, x⟫) Finset.univ_nonempty
  have hS : (Finset.univ.filter (fun j => ⟪v j, x⟫ = ⟪v m, x⟫)).Nonempty := ⟨m, by simp⟩
  set i := (Finset.univ.filter (fun j => ⟪v j, x⟫ = ⟪v m, x⟫)).min' hS with hi
  have hiS : i ∈ Finset.univ.filter (fun j => ⟪v j, x⟫ = ⟪v m, x⟫) := Finset.min'_mem _ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiS
  refine ⟨i, ⟨fun j => hiS ▸ hm j (Finset.mem_univ _), fun j hj => ?_⟩, ?_⟩
  · rcases lt_or_eq_of_le (hm j (Finset.mem_univ _)) with h | h
    · rw [hiS]; exact h
    · exfalso
      have : i ≤ j := Finset.min'_le _ _ (by simp [h])
      exact absurd hj (not_lt.mpr this)
  · rintro i' ⟨h1, h2⟩
    have e' : ⟪v i', x⟫ = ⟪v m, x⟫ := le_antisymm (hm i' (Finset.mem_univ _)) (h1 m)
    rcases lt_trichotomy i' i with h | h | h
    · exfalso
      have : i ≤ i' := Finset.min'_le _ _ (by simp [e'])
      exact absurd h (not_lt.mpr this)
    · exact h
    · exfalso
      have := h2 i h
      rw [hiS, e'] at this
      exact lt_irrefl _ this

