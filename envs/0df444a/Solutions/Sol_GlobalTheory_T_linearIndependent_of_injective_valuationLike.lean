-- Prove2me | solution 1 for GlobalTheory.T.linearIndependent_of_injective_valuationLike
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:47.757804+00:00
-- url     : https://prove2.me/submissions/b795a87e-34ca-4301-bf14-4e05500a8af6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLike
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Theorems.Thm_GlobalTheory_linearIndependent_of_distinct_valuationLike


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C V Γ ι : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → ∀ f : ι → V, (∀ i, f i ≠ 0) → Function.Injective (fun i => ν (f i)) → LinearIndependent C f := by
  first | exact @GlobalTheory.linearIndependent_of_distinct_valuationLike | exact GlobalTheory.linearIndependent_of_distinct_valuationLike | (intros; apply GlobalTheory.linearIndependent_of_distinct_valuationLike <;> assumption)
end _root_.GlobalTheory.T
