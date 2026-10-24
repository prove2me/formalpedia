-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_span_support_for_family
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:29:57.007912+00:00
-- url     : https://prove2.me/submissions/1ba80063-a2cc-4f48-819d-b32ececb4cea

import Mathlib

universe u v w

theorem solution
    {R : Type u} [CommSemiring R]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {α : Type w}
    (y : ι → R) (P : α → Prop) (g : α → R)
    (h : ∀ i : ι, y i ∈ Ideal.span (Set.range (fun a : {a // P a} => g a.1))) :
    ∃ k : Nat, ∃ f : Fin k → {a // P a},
      ∀ i : ι, y i ∈ Ideal.span (Set.range (fun j : Fin k => g (f j).1)) := by
  classical
  have hT : ∀ i, ∃ T : Finset R, (T : Set R) ⊆ Set.range (fun a : {a // P a} => g a.1) ∧
      y i ∈ Ideal.span (T : Set R) := fun i => Submodule.mem_span_finite_of_mem_span (h i)
  choose T hTsub hTmem using hT
  set U : Finset R := Finset.univ.biUnion T with hU
  have hUsub : ∀ r : U, ∃ a : {a // P a}, g a.1 = r := by
    rintro ⟨r, hr⟩
    rw [hU, Finset.mem_biUnion] at hr
    obtain ⟨i, _, hi⟩ := hr
    exact hTsub i hi
  choose pre hpre using hUsub
  refine ⟨U.card, fun j => pre (U.equivFin.symm j), fun i => ?_⟩
  refine Ideal.span_mono ?_ (hTmem i)
  intro r hr
  have hrU : r ∈ U := by
    rw [hU, Finset.mem_biUnion]; exact ⟨i, Finset.mem_univ _, hr⟩
  refine ⟨U.equivFin ⟨r, hrU⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hpre ⟨r, hrU⟩
