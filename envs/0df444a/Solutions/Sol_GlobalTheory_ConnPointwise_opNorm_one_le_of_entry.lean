-- Prove2me | solution 1 for GlobalTheory.ConnPointwise.opNorm_one_le_of_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:53.503114+00:00
-- url     : https://prove2.me/submissions/dbc4139c-c416-4c7c-9243-b060ad6d4b90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLe
import Theorems.Thm_GlobalTheory_ConnPointwise_gnorm_one_eq
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.ConnPointwise
variable {g : ℕ}
namespace GlobalTheory.ConnPointwise
theorem _root_.solution (M : Matrix (Fin g) (Fin g) ℂ) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ j k, ‖M j k‖ ≤ E) : opNorm 1 1 M ≤ g * E := by
  refine opNorm_le_of_bound (by positivity) fun v => ?_
  rw [gnorm_one_eq, gnorm_one_eq]
  set S := ∑ a, ‖v a‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrw : (g : ℝ) * E * √S = √(((g : ℝ) * E) ^ 2 * S) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hrw]
  apply Real.sqrt_le_sqrt
  have hrow : ∀ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ E ^ 2 * (g * S) := fun j => by
    have h1 : ‖(M *ᵥ v) j‖ ≤ E * ∑ k, ‖v k‖ := by
      rw [Finset.mul_sum]
      simp only [mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h j k) (norm_nonneg _)
    have h2 : (∑ k, ‖v k‖) ^ 2 ≤ g * S := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v k‖)
      simpa [hS] using this
    calc ‖(M *ᵥ v) j‖ ^ 2 ≤ (E * ∑ k, ‖v k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = E ^ 2 * (∑ k, ‖v k‖) ^ 2 := by ring
      _ ≤ E ^ 2 * (g * S) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  calc ∑ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ ∑ _j : Fin g, E ^ 2 * (g * S) := Finset.sum_le_sum fun j _ => hrow j
    _ = ((g : ℝ) * E) ^ 2 * S := by simp; ring
end GlobalTheory.ConnPointwise
