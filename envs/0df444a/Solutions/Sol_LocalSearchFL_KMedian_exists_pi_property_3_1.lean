-- Prove2me | solution 1 for LocalSearchFL.KMedian.exists_pi_property_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:45:54.759171+00:00
-- url     : https://prove2.me/submissions/db9bff9c-fffa-4530-97ff-0fa67ee7315c

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures

namespace LocalSearchFL.KMedian

open Classical in
theorem aux_pi31_hall {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (o : Fa) :
    ∃ f : {x // x ∈ nbhd σO o} → Cl, Function.Injective f ∧
      ∀ x, f x ∈ nbhd σO o ∧ (captures σS σO (σS x.1) o ∨ σS (f x) ≠ σS x.1) := by
  classical
  set N := nbhd σO o with hN
  suffices H : ∃ f : {x // x ∈ N} → Cl, Function.Injective f ∧
      ∀ x, f x ∈ N.filter (fun j' => captures σS σO (σS x.1) o ∨ σS j' ≠ σS x.1) by
    obtain ⟨f, hf1, hf2⟩ := H
    exact ⟨f, hf1, fun x => Finset.mem_filter.1 (hf2 x)⟩
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun x : {x // x ∈ N} =>
      N.filter (fun j' => captures σS σO (σS x.1) o ∨ σS j' ≠ σS x.1))).1
  intro s
  have hsN : s.card ≤ N.card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro x _; exact x.2
    · intro x _ y _ h; exact Subtype.ext h
  by_cases h : N ⊆ s.biUnion (fun x : {x // x ∈ N} =>
      N.filter (fun j' => captures σS σO (σS x.1) o ∨ σS j' ≠ σS x.1))
  · exact hsN.trans (Finset.card_le_card h)
  · rw [Finset.not_subset] at h
    obtain ⟨j', hj'N, hj'⟩ := h
    rcases s.eq_empty_or_nonempty with hs | ⟨j0, hj0⟩
    · simp [hs]
    have key : ∀ x ∈ s, ¬ captures σS σO (σS x.1) o ∧ σS j' = σS x.1 := by
      intro x hx
      have : j' ∉ N.filter (fun j'' => captures σS σO (σS x.1) o ∨ σS j'' ≠ σS x.1) := by
        intro hmem; exact hj' (Finset.mem_biUnion.2 ⟨x, hx, hmem⟩)
      simp only [Finset.mem_filter, not_and, not_or, not_not] at this
      exact this hj'N
    set a := σS j' with ha
    have hk : s.card ≤ (N.filter (fun j => σS j = a)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter]
        exact ⟨x.2, ((key x hx).2).symm⟩
      · intro x _ y _ h; exact Subtype.ext h
    have hcap : ¬ captures σS σO a o := by
      have := (key j0 hj0); rw [this.2]; exact this.1
    have hinter : N ∩ nbhd σS a = N.filter (fun j => σS j = a) := by
      ext j; simp [nbhd]
    have h2 : 2 * (N.filter (fun j => σS j = a)).card ≤ N.card := by
      unfold captures at hcap; rw [← hN, hinter] at hcap; omega
    have hsplit := Finset.card_filter_add_card_filter_not (s := N) (fun j => σS j = a)
    have hsub : N.filter (fun j => ¬ σS j = a) ⊆ s.biUnion (fun x : {x // x ∈ N} =>
        N.filter (fun j' => captures σS σO (σS x.1) o ∨ σS j' ≠ σS x.1)) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      refine Finset.mem_biUnion.2 ⟨j0, hj0, ?_⟩
      rw [Finset.mem_filter]
      refine ⟨hj.1, Or.inr ?_⟩
      rw [← (key j0 hj0).2]; exact hj.2
    have := Finset.card_le_card hsub
    omega

end LocalSearchFL.KMedian

open LocalSearchFL.KMedian

theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (o : Fa) :
    ∃ π : Equiv.Perm Cl,
      (∀ j, π j ∈ nbhd σO o ↔ j ∈ nbhd σO o) ∧
      (∀ j, j ∉ nbhd σO o → π j = j) ∧
      ∀ s : Fa, ¬ captures σS σO s o →
        ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∉ nbhd σO o ∩ nbhd σS s := by
  obtain ⟨f, hinj, hf⟩ := aux_pi31_hall σS σO o
  have hfN : ∀ x, f x ∈ nbhd σO o := fun x => (hf x).1
  let g : {x // x ∈ nbhd σO o} → {x // x ∈ nbhd σO o} := fun x => ⟨f x, hfN x⟩
  have hg : Function.Injective g := by
    intro x y h; exact hinj (congrArg Subtype.val h)
  let e : Equiv.Perm {x // x ∈ nbhd σO o} := Equiv.ofBijective g hg.bijective_of_finite
  refine ⟨Equiv.Perm.ofSubtype e, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ nbhd σO o
    · rw [Equiv.Perm.ofSubtype_apply_of_mem e hj]
      simp only [hj, iff_true]
      exact (e ⟨j, hj⟩).2
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem e hj]
  · intro j hj; exact Equiv.Perm.ofSubtype_apply_of_not_mem e hj
  · intro s hs j hj
    rw [Finset.mem_inter] at hj
    rw [Equiv.Perm.ofSubtype_apply_of_mem e hj.1]
    have h1 := hf ⟨j, hj.1⟩
    have hsj : σS j = s := by simpa [nbhd] using hj.2
    intro hmem
    rw [Finset.mem_inter] at hmem
    have hs2 : σS (f ⟨j, hj.1⟩) = s := by
      have := hmem.2
      simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    rcases h1.2 with h | h
    · exact hs (hsj ▸ h)
    · exact h (hs2.trans hsj.symm)
