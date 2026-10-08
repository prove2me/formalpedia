-- Prove2me | solution 1 for HryniewiczCriterion.monotoneOn_Icc_of_forall_local
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:56:37.609675+00:00
-- url     : https://prove2.me/submissions/9d8e9037-2dc9-48d5-9157-37118e7ced7b

import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Interval.Set.Infinite



/-!
# Leaf C2, part 0: local monotonicity on `[0, T]` implies monotonicity
-/

namespace HryniewiczCriterion

open Set

/-- Local monotonicity on `[0, T]` implies monotonicity (Lebesgue number lemma). -/
theorem monotoneOn_Icc_of_local {E : ℝ → ℝ} {T : ℝ}
    (h : ∀ t0 ∈ Icc 0 T, ∃ δ > 0, ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T →
      |s - t0| < δ → |t - t0| < δ → s ≤ t → E s ≤ E t) :
    MonotoneOn E (Icc 0 T) := by
  choose! δ hδ hloc using h
  obtain ⟨r, hr, hcov⟩ := lebesgue_number_lemma_of_metric (c := fun t0 : Icc (0 : ℝ) T =>
      Metric.ball (t0 : ℝ) (δ t0)) isCompact_Icc (fun _ => Metric.isOpen_ball)
    (fun t ht => Set.mem_iUnion.mpr ⟨⟨t, ht⟩, Metric.mem_ball_self (hδ t ht)⟩)
  have close : ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t → t - s < r → E s ≤ E t := by
    intro s t hs ht hst hlt
    obtain ⟨⟨t0, ht0⟩, hball⟩ := hcov s hs
    have hs' := hball (Metric.mem_ball_self hr)
    have ht' := hball (show t ∈ Metric.ball s r by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    simp only [Metric.mem_ball, Real.dist_eq] at hs' ht'
    exact hloc t0 ht0 s t hs ht hs' ht' hst
  have step : ∀ k : ℕ, ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t → t - s < k * (r / 2) →
      E s ≤ E t := by
    intro k
    induction k with
    | zero => intro s t _ _ hst hlt; simp at hlt; linarith
    | succ k ih =>
      intro s t hs ht hst hlt
      by_cases hc : t - s < r / 2
      · exact close s t hs ht hst (by linarith)
      · push_neg at hc
        have hu : s + r / 2 ∈ Icc 0 T := ⟨by linarith [hs.1], by linarith [ht.2]⟩
        refine (close s (s + r / 2) hs hu (by linarith) (by linarith)).trans
          (ih (s + r / 2) t hu ht (by linarith) ?_)
        push_cast at hlt; linarith
  intro s hs t ht hst
  obtain ⟨k, hk⟩ := exists_nat_gt (T / (r / 2))
  refine step k s t hs ht hst ?_
  have : T < k * (r / 2) := by rwa [div_lt_iff₀ (by linarith)] at hk
  linarith [hs.1, ht.2]

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution {E : ℝ → ℝ} {T : ℝ}
    (h : ∀ t0 ∈ Set.Icc 0 T, ∃ δ > 0, ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      |s - t0| < δ → |t - t0| < δ → s ≤ t → E s ≤ E t) :
    MonotoneOn E (Set.Icc 0 T) :=
  monotoneOn_Icc_of_local h
