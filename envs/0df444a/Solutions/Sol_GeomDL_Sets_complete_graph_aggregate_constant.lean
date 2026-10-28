-- Prove2me | solution 1 for GeomDL.Sets.complete_graph_aggregate_constant
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:37:56.287763+00:00
-- url     : https://prove2.me/submissions/2bdf61d9-8e67-4ea3-9219-187a091b23de

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

open GeomDL.Sets

theorem solution {n d : ℕ} {M M' : Type*}
    (ψ : (Fin d → ℝ) → M) (agg : Multiset M → M')
    (X : Matrix (Fin n) (Fin d) ℝ) :
    ∀ u w : Fin n,
      agg ((neighbourhood (allOnes n) u).val.map (fun v => ψ (X v))) =
        agg ((neighbourhood (allOnes n) w).val.map (fun v => ψ (X v))) := by
  have h : ∀ u, neighbourhood (allOnes n) u = Finset.univ := by
    intro u; ext v; simp [neighbourhood, allOnes]
  intro u w
  rw [h u, h w]
