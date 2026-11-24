-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DiracComb.exists_unity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:53.994631+00:00
-- url     : https://prove2.me/submissions/bb8d5403-4717-44a0-b7f3-b6a8d65cfab4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DenseHasCompactSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DiracComb
namespace GlobalTheory.CompanionTheory.DiracComb
theorem _root_.solution (n : ℕ) : ∃ ρ : (Fin n → ℤ) → (Fin n → ℝ) → ℝ, (∀ m, ContDiff ℝ ∞ (ρ m)) ∧
    (∀ m, tsupport (ρ m) ⊆ Metric.ball (fun i => (m i : ℝ)) 1) ∧
    LocallyFinite (fun m => Function.support (ρ m)) ∧ ∀ x, ∑ᶠ m, ρ m x = 1 := by
  have hcov : (Set.univ : Set (Fin n → ℝ)) ⊆
      ⋃ m : Fin n → ℤ, Metric.ball (fun i => (m i : ℝ)) 1 := by
    intro x _
    refine Set.mem_iUnion.2 ⟨fun i => ⌊x i⌋, ?_⟩
    rw [Metric.mem_ball, dist_pi_lt_iff one_pos]
    intro i
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [Int.floor_le (x i), Int.lt_floor_add_one (x i)]
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Fin n → ℝ)) isClosed_univ
    (fun m : Fin n → ℤ => Metric.ball (fun i => (m i : ℝ)) 1) (fun _ => Metric.isOpen_ball) hcov
  exact ⟨fun m => ρ m, fun m => (ρ m).contMDiff.contDiff, hρ, ρ.locallyFinite,
    fun x => ρ.sum_eq_one (Set.mem_univ x)⟩
end GlobalTheory.CompanionTheory.DiracComb
