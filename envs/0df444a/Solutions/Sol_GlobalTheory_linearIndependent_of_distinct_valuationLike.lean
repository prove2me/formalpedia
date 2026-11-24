-- Prove2me | solution 1 for GlobalTheory.linearIndependent_of_distinct_valuationLike
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:18:09.227045+00:00
-- url     : https://prove2.me/submissions/352ffe13-5395-4bf4-8107-fee08a2eee5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLike

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
    ∀ (C V Γ ι : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ),
      (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) →
      (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) →
      ∀ f : ι → V, (∀ i, f i ≠ 0) → Function.Injective (fun i => ν (f i)) →
        LinearIndependent C f := by
  intro C V Γ ι _ _ _ _ ν hsm hadd f hf hinj
  classical
  have key : ∀ (g : ι → C) (s : Finset ι), s.Nonempty → (∀ i ∈ s, g i ≠ 0) →
      (∑ i ∈ s, g i • f i) ≠ 0 ∧ ∃ j ∈ s, ν (∑ i ∈ s, g i • f i) = ν (f j) := by
    intro g s
    induction s using Finset.induction_on with
    | empty => intro h; exact absurd h Finset.not_nonempty_empty
    | @insert a s ha ih =>
      intro _ hg
      have hga : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
      have hx : g a • f a ≠ 0 := smul_ne_zero hga (hf a)
      have hνx : ν (g a • f a) = ν (f a) := hsm _ _ hga
      rw [Finset.sum_insert ha]
      rcases s.eq_empty_or_nonempty with hs | hs
      · subst hs
        simp only [Finset.sum_empty, add_zero]
        exact ⟨hx, a, Finset.mem_insert_self a _, hνx⟩
      · obtain ⟨hy, j, hj, hνy⟩ := ih hs (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        have hne : ν (f a) ≠ ν (f j) := by
          intro h
          have : a = j := hinj h
          exact ha (this ▸ hj)
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · obtain ⟨h1, h2⟩ := hadd _ _ hx hy (by rw [hνx, hνy]; exact hlt)
          exact ⟨h1, a, Finset.mem_insert_self a s, by rw [h2, hνx]⟩
        · obtain ⟨h1, h2⟩ := hadd _ _ hy hx (by rw [hνx, hνy]; exact hlt)
          refine ⟨by rw [add_comm]; exact h1, j, Finset.mem_insert_of_mem hj, ?_⟩
          rw [add_comm, h2, hνy]
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have hsum' : ∑ k ∈ s.filter (fun k => g k ≠ 0), g k • f k = 0 := by
    rw [Finset.sum_filter_of_ne]
    · exact hsum
    · intro x _ hx h
      apply hx
      simp [h]
  have hne : (s.filter (fun k => g k ≠ 0)).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hgi⟩⟩
  exact (key g _ hne (fun j hj => (Finset.mem_filter.1 hj).2)).1 hsum'
end GlobalTheory
