-- Prove2me | solution 1 for GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:35.945037+00:00
-- url     : https://prove2.me/submissions/b11a6e89-d46f-43c4-b23f-6f44eb111af1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
import Theorems.Thm_GlobalTheory_eventually_forall_norm_iteratedFDeriv_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {X : Type} [TopologicalSpace X] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : X → SchwartzMap V ℂ) (x0 : X), (∀ v, ContinuousAt (fun x => F x v) x0) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in nhds x0, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x) v‖ ≤ C) → ContinuousAt F x0 := by
  intro X _ V _ _ _ F x0 hc hb
  have hb' : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in nhds x0, ∀ v,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ ≤ C := by
    intro k n
    obtain ⟨C, hC⟩ := hb k n
    refine ⟨max C 0 + SchwartzMap.seminorm ℝ k n (F x0), add_nonneg (le_max_right _ _) (apply_nonneg _ _), ?_⟩
    filter_upwards [hC] with x hx v
    calc _ ≤ SchwartzMap.seminorm ℝ k n (F x - F x0) := SchwartzMap.le_seminorm ℝ k n _ v
      _ ≤ SchwartzMap.seminorm ℝ k n (F x) + SchwartzMap.seminorm ℝ k n (F x0) := map_sub_le_add _ _ _
      _ ≤ _ := add_le_add (SchwartzMap.seminorm_le_bound ℝ k n (F x) (le_max_right _ _)
          (fun w => (hx w).trans (le_max_left _ _))) le_rfl
  have hp : ∀ v, Tendsto (fun x => (F x - F x0) v) (nhds x0) (𝓝 0) := by
    intro v
    have h2 := (hc v).tendsto.sub_const (F x0 v)
    rw [sub_self] at h2
    exact h2
  rw [ContinuousAt, (schwartz_withSeminorms ℝ V ℂ).tendsto_nhds F (F x0)]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨C2, hC20, hC2⟩ := hb' (2 * k) n
  have hη : 0 < ε ^ 2 / (4 * (C2 + 1)) := div_pos (pow_pos hε 2) (by linarith)
  have hCη : C2 * (ε ^ 2 / (4 * (C2 + 1))) ≤ (ε / 2) ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg ε]
  filter_upwards [eventually_forall_norm_iteratedFDeriv_le (h := fun x => F x - F x0) hp hb' n _ hη, hC2]
    with x hx hx2
  show SchwartzMap.seminorm ℝ k n (F x - F x0) < ε
  refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n _ (by linarith : (0 : ℝ) ≤ ε / 2)
    (fun v => ?_)) (by linarith)
  have ha : 0 ≤ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ := by positivity
  have hsq : (‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) ^ 2 ≤ (ε / 2) ^ 2 := by
    have e : (‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) ^ 2 =
        (‖v‖ ^ (2 * k) * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ := by
      rw [pow_mul']
      ring
    rw [e]
    exact (mul_le_mul (hx2 v) (hx v) (norm_nonneg _) hC20).trans hCη
  nlinarith
end GlobalTheory
