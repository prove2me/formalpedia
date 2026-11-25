-- Prove2me | solution 1 for GlobalTheory.mem_span_iff_finrank_option_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:44.437804+00:00
-- url     : https://prove2.me/submissions/50c7ada7-f3c8-48db-988d-f618be208cf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LinearIndependentRingHomCompIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F V ι : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (v : Option ι → V) :
    v none ∈ Submodule.span F (Set.range fun i => v (some i)) ↔
      Module.finrank F (Submodule.span F (Set.range fun i => v (some i))) =
        Module.finrank F (Submodule.span F (Set.range v)) := by
  have hle : Submodule.span F (Set.range fun i => v (some i)) ≤ Submodule.span F (Set.range v) := by
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨some k, rfl⟩
  constructor
  · intro h
    have : Submodule.span F (Set.range fun i => v (some i)) = Submodule.span F (Set.range v) := by
      refine le_antisymm hle (Submodule.span_le.2 ?_)
      rintro _ ⟨_ | k, rfl⟩
      · exact h
      · exact Submodule.subset_span ⟨k, rfl⟩
    rw [this]
  · intro h
    rw [Submodule.eq_of_le_of_finrank_eq hle h]
    exact Submodule.subset_span ⟨none, rfl⟩
end GlobalTheory
