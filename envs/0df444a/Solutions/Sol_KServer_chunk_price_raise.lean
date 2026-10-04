-- Prove2me | solution 1 for KServer.chunk_price_raise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T12:46:07.440115+00:00
-- url     : https://prove2.me/submissions/321362d5-a08d-4885-8928-1e1693743235

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

open KServer

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price price' : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo) (hP : price ≤ price') :
    ∃ C' : ChunkSystemB X s t cLo cHi total price' mLo, C'.m = C.m :=
  ⟨{ C with
      hcost := by
        have key : ∀ (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (h χ : List (Set X))
            (p p' : ℝ), p ≤ p' → E.bailCost bail h χ p ≤ E.bailCost bail h χ p' := by
          intro E bail h χ p p' hp
          unfold EvaderAlgorithm.bailCost
          generalize hbt : bailTime bail h χ = k
          cases k with
          | none => exact le_rfl
          | some q =>
              simpa only [add_comm] using
                (add_le_add_left hp (E.costOn h (List.take q χ)))
        intro i ω₀ E bail
        refine le_trans (C.hcost i ω₀ E bail) ?_
        refine Finset.sum_le_sum ?_
        intro ω _
        exact mul_le_mul_of_nonneg_left
          (key E bail ((List.ofFn (C.chunk ω)).take i).flatten (C.chunk ω i) price price' hP)
          (le_of_lt (C.hP ω)) }, rfl⟩
