-- Prove2me | solution 1 for GlobalTheory.AffineThickening.exists_forall_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:04:51.338226+00:00
-- url     : https://prove2.me/submissions/2f6caf19-9e22-4a81-9096-b12a170ac94e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}
namespace GlobalTheory.AffineThickening
theorem _root_.solution {α : Type*} [Finite α] (P : α → ℕ → Prop)
    (hP : ∀ a n, P a n → P a (n + 1)) (h : ∀ a, ∃ n, P a n) : ∃ n, ∀ a, P a n := by
  choose n hn using h
  obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
  exact ⟨N, fun a ↦ Nat.le_induction (hn a) (fun m _ ↦ hP a m) N (hN ⟨a, rfl⟩)⟩
end GlobalTheory.AffineThickening
