-- Prove2me | solution 1 for GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:04:52.357212+00:00
-- url     : https://prove2.me/submissions/70f4d8ef-cbeb-491b-b176-27dc677d5e09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentAdaptedToDecreasingChainA
import Theorems.Thm_GlobalTheory_exists_linearIndependent_extend_with_levels

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
theorem _root_.solution : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G]
    (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ),
    (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) →
    (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ),
      LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧
      ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  intro G _ _ S hS N
  induction N generalizing S with
  | zero =>
    intro r hr _
    obtain ⟨e, he, heS⟩ := hr 0
    exact ⟨e, fun _ => 0, he, heS, by simp⟩
  | succ N ih =>
    intro r hr hrd
    obtain ⟨e', n', he', heS', hsum⟩ := ih (fun i => S (i + 1)) (fun i => hS (i + 1))
      (fun i => r (i + 1)) (fun i => hr (i + 1)) (fun i => hrd (i + 1))
    obtain ⟨f, hf, hfS⟩ := hr 0
    obtain ⟨e, n, he, heS, hn⟩ := exists_linearIndependent_extend_with_levels S f hf hfS (r (0 + 1)) e' (fun j => n' j + 1) he'
      heS' (r 0) (hrd 0) le_rfl
    refine ⟨e, n, he, heS, ?_⟩
    rw [Finset.sum_range_succ']
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hsum hn ⊢
    omega
end GlobalTheory
