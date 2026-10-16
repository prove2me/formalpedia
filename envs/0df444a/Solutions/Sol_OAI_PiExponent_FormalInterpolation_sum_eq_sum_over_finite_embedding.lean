-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.sum_eq_sum_over_finite_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:12:02.664396+00:00
-- url     : https://prove2.me/submissions/cf791ee2-dbe5-49c3-a601-3f9d011518b4

import Mathlib

open scoped BigOperators

theorem solution
    {α β R : Type*} [DecidableEq α] [Fintype β] [CommSemiring R]
    (S : Finset α) (f : β → α) (a g : α → R)
    (hf : Function.Injective f)
    (hcover : ∀ x ∈ S, ∃ b, f b = x)
    (hzero : ∀ x, x ∉ S → a x = 0) :
      ∑ x ∈ S, a x * g x = ∑ b : β, g (f b) * a (f b) := by
  classical
  let T : Finset β := Finset.univ.filter (fun b => f b ∈ S)
  calc
    ∑ x ∈ S, a x * g x = ∑ b ∈ T, g (f b) * a (f b) := by
      symm
      apply Finset.sum_bij (fun b _ => f b)
      · intro b hb
        exact (Finset.mem_filter.mp hb).2
      · intro b₁ hb₁ b₂ hb₂ h
        exact hf h
      · intro x hx
        obtain ⟨b, hb⟩ := hcover x hx
        refine ⟨b, ?_, hb⟩
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        · rw [hb]
          exact hx
      · intro b hb
        simp [mul_comm]
    _ = ∑ b : β, g (f b) * a (f b) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro b hb hnot
      have hnotS : f b ∉ S := by
        intro hfb
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfb⟩)
      simp [hzero (f b) hnotS]
