-- Prove2me | solution 1 for GlobalTheory.DecayOfMemSpan.decay_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:44.430843+00:00
-- url     : https://prove2.me/submissions/3489c825-9c26-4e7c-8b9a-60a077b23a16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DecayOfMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DecayOfMemSpan
namespace GlobalTheory.DecayOfMemSpan
theorem _root_.solution {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : G → H →L[ℂ] H} {D : G → ℝ} {c : ℝ} {S : Set H} {u : H}
    (h : ∀ v ∈ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g))) :
    ∀ v ∈ Submodule.span ℂ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g)) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, fun g => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    refine ⟨A + B, fun g => ?_⟩
    rw [inner_add_left, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hA g) (hB g))
  | smul a x _ hx =>
    obtain ⟨A, hA⟩ := hx
    refine ⟨‖a‖ * A, fun g => ?_⟩
    rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA g) (norm_nonneg a)
end GlobalTheory.DecayOfMemSpan
