-- Prove2me | solution 1 for GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:51.148866+00:00
-- url     : https://prove2.me/submissions/c2427475-d620-4674-8725-0bd7d679454f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultisetManySeparatedPoints
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultisetManySeparatedPointsStatement
import Theorems.Thm_GlobalTheory_multiset_many_separated_points


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  first | exact @GlobalTheory.multiset_many_separated_points | exact GlobalTheory.multiset_many_separated_points | (intros; apply GlobalTheory.multiset_many_separated_points <;> assumption)
end _root_.GlobalTheory.T
