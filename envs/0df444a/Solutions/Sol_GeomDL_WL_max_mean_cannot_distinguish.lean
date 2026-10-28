-- Prove2me | solution 1 for GeomDL.WL.max_mean_cannot_distinguish
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:51:58.265841+00:00
-- url     : https://prove2.me/submissions/9b297c39-c736-4b2a-8ff2-0216dd09d948

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_GeomDL_WL_Defs

open GeomDL.WL

theorem solution {d : ℕ} (a b : Fin d → ℝ) :
    ({a, b} : Multiset (Fin d → ℝ)) ≠ {a, a, b, b} ∧
      maxAgg ({a, b} : Multiset (Fin d → ℝ)) = maxAgg {a, a, b, b} ∧
      meanAgg ({a, b} : Multiset (Fin d → ℝ)) = meanAgg {a, a, b, b} := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have := congrArg Multiset.card h
    simp at this
  · simp [maxAgg, Multiset.bind, Multiset.sup_cons]
  · simp only [meanAgg, Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton,
      Multiset.sum_cons, Multiset.sum_singleton]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast
    ring
