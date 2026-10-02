-- Prove2me | solution 5 for MilnorDynamics.normal_disk_to_thrice_punctured_plane
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T08:27:16.32843+00:00
-- url     : https://prove2.me/submissions/6333588e-32d5-4986-8c2b-42328566f21b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_locally_bounded_holomorphic_subseq_locally_uniform
import Theorems.Thm_MilnorDynamics_either_limit_avoids_or_diverges
import Theorems.Thm_MilnorDynamics_not_locally_bounded_subseq_diverges
import Theorems.Thm_isSimplyConnected_unitDisc

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- **Milnor's Corollary 3.3, assembled from the two halves of the dichotomy.**

`IsNormalFamilyInto` asks, for each sequence in the family, for a subsequence that either
converges locally uniformly to a continuous map still landing outside {0, 1}, or diverges
locally uniformly from that target.  The two disjuncts come from the two halves of the
dichotomy, and the case split is on whether the family is locally bounded. -/
theorem solution (𝓕 : Set (ℂ → ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      MapsTo f (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) :
    IsNormalFamilyInto (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) 𝓕 := by
  -- The source is connected: the open unit disc is simply connected, hence path connected.
  have hball : IsOpen (Metric.ball 0 1 : Set ℂ) := Metric.isOpen_ball
  have hUc : IsConnected (Metric.ball 0 1 : Set ℂ) :=
    isSimplyConnected_unitDisc.isPathConnected.isConnected
  intro f hf
  have hfam : ∀ n, DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧
      MapsTo (f n) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) :=
    fun n => h𝓕 (f n) (hf n)
  by_cases hb : ∀ K ⊆ Metric.ball 0 1, IsCompact K →
      ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M
  · -- Locally bounded: Arzela-Ascoli gives a locally uniform limit, and the Hurwitz
    -- dichotomy says that limit either still omits 0 and 1, or the sequence diverges.
    obtain ⟨φ, hφ, g, hg, hconv⟩ :=
      locally_bounded_holomorphic_subseq_locally_uniform (Metric.ball 0 1) hball f
        (fun n => (hfam n).1) hb
    rcases either_limit_avoids_or_diverges (Metric.ball 0 1) hball hUc
      (fun n => f (φ n)) (fun n => hfam (φ n)) g hg hconv with hmaps | hdiv
    · exact ⟨φ, hφ, Or.inl ⟨g, hg, hmaps, hconv⟩⟩
    · exact ⟨φ, hφ, Or.inr hdiv⟩
  · -- Not locally bounded: the escape branch, an Open node of this milestone.
    have hbdd : ∃ K ⊆ Metric.ball 0 1, IsCompact K ∧
        ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) := by
      rcases not_forall.mp hb with ⟨K, hK⟩
      -- `hK : ¬(K ⊆ _ → IsCompact K → ∃ M, _)` must supply
      -- `K ⊆ _ ∧ IsCompact K ∧ ¬∃ M, _`.  Two separate defects caused the
      -- earlier `simpa only [not_imp] using hK` to fail:
      --   * unqualified `not_imp` is ambiguous -- the root, `Classical`, and
      --     Mathlib's `Push` namespace each declare one;
      --   * even resolved, it only gives `¬(IsCompact K → _)` as the second
      --     conjunct, which is still a *negated implication* and so does not
      --     match the `IsCompact K ∧ ¬∃ M, _` the child expects.
      -- So split the outer negation structurally, and discharge the last two
      -- goals by hand, never rewriting through `not_imp`.
      have hsplit : K ⊆ Metric.ball 0 1 ∧
          ¬ (IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :=
        Classical.not_imp.mp hK
      have hKn : ¬ (IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :=
        hsplit.2
      have hsub : K ⊆ Metric.ball 0 1 := hsplit.1
      -- Peel the negated implication once more: `not_imp` turns
      -- `not(IsCompact K -> exists M, _)` into exactly
      -- `IsCompact K /\ not exists M, _`, which is the conjunction the child
      -- requires.  A previous revision built this with `refine <K, ..., _, _>`
      -- plus `by_contra` on each field.  Because `hKn` negates the *whole*
      -- implication, `by_contra` inverted that outer negation and produced
      -- `not(IsCompact K)` and an implication-shaped goal, which Lean rejected
      -- both times (E01: supplied `not IsCompact K` where
      -- `IsCompact K -> exists M, ...` was expected; E02: `not an inductive type`).
      -- Peeling with `not_imp` avoids negation reasoning entirely.
      exact ⟨K, hsub, Classical.not_imp.mp hKn⟩
    obtain ⟨φ, hφ, hdiv⟩ :=
      not_locally_bounded_subseq_diverges (Metric.ball 0 1) hball hUc f hfam hbdd
    exact ⟨φ, hφ, Or.inr hdiv⟩
