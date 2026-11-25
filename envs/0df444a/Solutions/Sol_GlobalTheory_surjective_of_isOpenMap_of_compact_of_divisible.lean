-- Prove2me | solution 1 for GlobalTheory.surjective_of_isOpenMap_of_compact_of_divisible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:46.978503+00:00
-- url     : https://prove2.me/submissions/8ab4593f-0fd6-4dea-b9eb-8aec71e06499

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V A : Type*} [NormedAddCommGroup V] [AddCommGroup A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] {e : V →+ A}
namespace GlobalTheory
theorem _root_.solution [CompactSpace A] (he : IsOpenMap e)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ a : A, ∃ b : A, n • b = a) : Function.Surjective e := by
  have : Finite (A ⧸ e.range) := e.range.quotient_finite_of_isOpen he.isOpen_range
  intro a
  obtain ⟨b, rfl⟩ := hdiv e.range.index AddSubgroup.index_ne_zero_of_finite a
  exact e.range.nsmul_index_mem b
end GlobalTheory
