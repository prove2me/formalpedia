-- Prove2me | solution 1 for OAI.C0Absorption.bounded_signs_weak_null
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:21:47.193358+00:00
-- url     : https://prove2.me/submissions/14ef483a-0bee-4dc9-971a-0719762f058a

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset


theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (u : X →L[ℝ] ℝ) : Filter.Tendsto (fun i => u (m i)) Filter.atTop (nhds 0) := by
  have hpart : ∀ n, ∑ i ∈ Finset.range n, |u (m i)| ≤ ‖u‖ * M := by
    intro n
    let ε : Fin n → Bool := fun i => decide (0 ≤ u (m i))
    have h1 : ∑ i ∈ Finset.range n, |u (m i)| = u (∑ i, realSign (ε i) • m i) := by
      rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun i => |u (m i)|)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, smul_eq_mul]
      by_cases h : 0 ≤ u (m i)
      · simp [ε, h, abs_of_nonneg h]
      · push_neg at h; simp [ε, h.not_ge, abs_of_neg h]
    rw [h1]
    calc u (∑ i, realSign (ε i) • m i) ≤ ‖u (∑ i, realSign (ε i) • m i)‖ := Real.le_norm_self _
      _ ≤ ‖u‖ * ‖∑ i, realSign (ε i) • m i‖ := u.le_opNorm _
      _ ≤ ‖u‖ * M := by gcongr; exact hsum n ε
  have hs : Summable (fun i => |u (m i)|) :=
    summable_of_sum_range_le (fun i => abs_nonneg _) hpart
  have := hs.tendsto_atTop_zero
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact this

