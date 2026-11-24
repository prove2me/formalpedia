-- Prove2me | solution 1 for GlobalTheory.exists_fin_independent_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:41:27.179229+00:00
-- url     : https://prove2.me/submissions/7a2064f8-6295-4606-aad2-e448ed18f628

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedTwoSubspaces

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
theorem _root_.solution {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Submodule K V) :
    ∃ (n : ℕ) (v : Fin n → V), LinearIndependent K v ∧ Submodule.span K (Set.range v) = S := by
  let b := Module.finBasis K S
  refine ⟨_, S.subtype ∘ b, b.linearIndependent.map' S.subtype (Submodule.ker_subtype S), ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
end GlobalTheory
