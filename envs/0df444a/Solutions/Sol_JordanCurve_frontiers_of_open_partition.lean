-- Prove2me | solution 1 for JordanCurve.frontiers_of_open_partition
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T00:17:31.630432+00:00
-- url     : https://prove2.me/submissions/c90b0af4-e8e0-4382-9a05-6fb6cd0a1c22

import Mathlib.Topology.Closure
import Mathlib.Topology.Connected.Basic

theorem solution {X : Type*} [TopologicalSpace X]
    (J U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : U ∪ V = Jᶜ)
    (haccess : J ⊆ closure U ∩ closure V) :
    frontier U = J ∧ frontier V = J := by
  have boundary (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
      (hAB : Disjoint A B) (hcov : A ∪ B = Jᶜ)
      (hacc : J ⊆ closure A) : frontier A = J := by
    have hAcomp : A ⊆ Jᶜ := by
      intro x hx
      rw [← hcov]
      exact Or.inl hx
    have hAnotB : A ⊆ Bᶜ := by
      intro x hxA hxB
      exact Set.disjoint_left.mp hAB hxA hxB
    apply Set.Subset.antisymm
    · intro x hx
      rw [hA.frontier_eq] at hx
      by_contra hxJ
      have hxAB : x ∈ A ∪ B := by
        rw [hcov]
        exact hxJ
      rcases hxAB with hxA | hxB
      · exact hx.2 hxA
      · exact ((hB.isClosed_compl.closure_subset_iff).2 hAnotB hx.1) hxB
    · intro x hxJ
      rw [hA.frontier_eq]
      exact ⟨hacc hxJ, fun hxA => hAcomp hxA hxJ⟩
  constructor
  · exact boundary U V hU hV hdisj hcover (fun x hx => (haccess hx).1)
  · apply boundary V U hV hU hdisj.symm
    · simpa only [Set.union_comm] using hcover
    · exact fun x hx => (haccess hx).2
