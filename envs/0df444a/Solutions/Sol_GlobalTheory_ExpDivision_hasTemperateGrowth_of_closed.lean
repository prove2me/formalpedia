-- Prove2me | solution 1 for GlobalTheory.ExpDivision.hasTemperateGrowth_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:53.317923+00:00
-- url     : https://prove2.me/submissions/a59bec41-5919-49fb-be70-dfa8d1ce2b63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution (S : Set (ℝ → ℂ))
    (hd : ∀ f ∈ S, Differentiable ℝ f) (hc : ∀ f ∈ S, deriv f ∈ S)
    (hb : ∀ f ∈ S, ∃ (k : ℕ) (C : ℝ), ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    {f : ℝ → ℂ} (hf : f ∈ S) : f.HasTemperateGrowth := by
  have hi : ∀ n, iteratedDeriv n f ∈ S := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih => rw [iteratedDeriv_succ]; exact hc _ ih
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => hd _ (hi m), fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hb _ (hi n)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact h x⟩
end GlobalTheory.ExpDivision
