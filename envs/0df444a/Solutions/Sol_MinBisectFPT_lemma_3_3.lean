-- Prove2me | solution 1 for MinBisectFPT.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T16:04:35.675209+00:00
-- url     : https://prove2.me/submissions/95a25061-b67a-4ecc-86b8-4615e77f1f96

import Mathlib

set_option autoImplicit false

private lemma key_compl {β : Type*} [DecidableEq β] (U V : Finset β) (hVU : V ⊆ U) :
    (∑ W ∈ U.powerset.filter (fun W => V ⊆ W), (-1 : ℤ) ^ (U \ W).card)
      = if U = V then 1 else 0 := by
  classical
  have hsum : (∑ W ∈ U.powerset.filter (fun W => V ⊆ W), (-1 : ℤ) ^ (U \ W).card)
      = ∑ S ∈ (U \ V).powerset, (-1 : ℤ) ^ S.card := by
    refine Finset.sum_bij'
      (fun W _ => U \ W) (fun S _ => U \ S) ?_ ?_ ?_ ?_ ?_
    · intro W hW
      rw [Finset.mem_powerset]
      intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      refine ⟨hx.1, ?_⟩
      intro hxV
      exact hx.2 ((Finset.mem_filter.mp hW).2 hxV)
    · intro S hS
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.sdiff_subset, ?_⟩
      intro x hxV
      rw [Finset.mem_sdiff]
      refine ⟨hVU hxV, ?_⟩
      intro hxS
      have hSU : S ⊆ U \ V := Finset.mem_powerset.mp hS
      exact absurd hxV (Finset.mem_sdiff.mp (hSU hxS)).2
    · intro W hW
      exact Finset.sdiff_sdiff_eq_self
        (Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1)
    · intro S hS
      exact Finset.sdiff_sdiff_eq_self
        ((Finset.mem_powerset.mp hS).trans Finset.sdiff_subset)
    · intro W hW
      rfl
  rw [hsum, Finset.sum_powerset_neg_one_pow_card]
  by_cases h : U = V
  · subst h
    simp
  · have hne : U \ V ≠ ∅ := by
      intro he
      exact h (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp he) hVU)
    simp [h, hne]

private lemma key_sub {β : Type*} [DecidableEq β] (U V : Finset β) (hVU : V ⊆ U) :
    (∑ W ∈ U.powerset.filter (fun W => V ⊆ W), (-1 : ℤ) ^ (W \ V).card)
      = if U = V then 1 else 0 := by
  classical
  have hsum : (∑ W ∈ U.powerset.filter (fun W => V ⊆ W), (-1 : ℤ) ^ (W \ V).card)
      = ∑ S ∈ (U \ V).powerset, (-1 : ℤ) ^ S.card := by
    refine Finset.sum_bij'
      (fun W _ => W \ V) (fun S _ => V ∪ S) ?_ ?_ ?_ ?_ ?_
    · intro W hW
      rw [Finset.mem_powerset]
      intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      refine ⟨?_, hx.2⟩
      exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1) hx.1
    · intro S hS
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, Finset.subset_union_left⟩
      exact Finset.union_subset hVU
        ((Finset.mem_powerset.mp hS).trans Finset.sdiff_subset)
    · intro W hW
      exact Finset.union_sdiff_of_subset (Finset.mem_filter.mp hW).2
    · intro S hS
      have hSU : S ⊆ U \ V := Finset.mem_powerset.mp hS
      ext x
      constructor
      · intro hx
        rw [Finset.mem_sdiff, Finset.mem_union] at hx
        rcases hx.1 with hxV | hxS
        · exact absurd hxV hx.2
        · exact hxS
      · intro hx
        rw [Finset.mem_sdiff, Finset.mem_union]
        exact ⟨Or.inr hx, fun hxV => (Finset.mem_sdiff.mp (hSU hx)).2 hxV⟩
    · intro W hW
      rfl
  rw [hsum, Finset.sum_powerset_neg_one_pow_card]
  by_cases h : U = V
  · subst h
    simp
  · have hne : U \ V ≠ ∅ := by
      intro he
      exact h (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp he) hVU)
    simp [h, hne]

private lemma swap_double_sum {β M : Type*} [DecidableEq β] [AddCommMonoid M]
    (U : Finset β) (F : Finset β → Finset β → M) :
    (∑ W ∈ U.powerset, ∑ V ∈ W.powerset, F W V)
      = ∑ V ∈ U.powerset, ∑ W ∈ U.powerset.filter (fun W => V ⊆ W), F W V := by
  classical
  calc (∑ W ∈ U.powerset, ∑ V ∈ W.powerset, F W V)
      = ∑ W ∈ U.powerset, ∑ V ∈ U.powerset.filter (fun V => V ⊆ W), F W V := by
        apply Finset.sum_congr rfl
        intro W hW
        have hpow : W.powerset = U.powerset.filter (fun V => V ⊆ W) := by
          ext V
          rw [Finset.mem_powerset, Finset.mem_filter, Finset.mem_powerset]
          constructor
          · intro hVW
            exact ⟨hVW.trans (Finset.mem_powerset.mp hW), hVW⟩
          · rintro ⟨-, hVW⟩
            exact hVW
        rw [hpow]
    _ = ∑ W ∈ U.powerset, ∑ V ∈ U.powerset, (if V ⊆ W then F W V else 0) := by
        apply Finset.sum_congr rfl
        intro W hW
        rw [Finset.sum_filter]
    _ = ∑ V ∈ U.powerset, ∑ W ∈ U.powerset, (if V ⊆ W then F W V else 0) :=
        Finset.sum_comm
    _ = ∑ V ∈ U.powerset, ∑ W ∈ U.powerset.filter (fun W => V ⊆ W), F W V := by
        apply Finset.sum_congr rfl
        intro V hV
        rw [Finset.sum_filter]

private lemma mobius_forward {β R : Type*} [Fintype β] [DecidableEq β] [AddCommGroup R]
    (g h : Finset β → R) (hg : ∀ W, g W = ∑ U ∈ W.powerset, h U) :
    ∀ U, h U = ∑ W ∈ U.powerset, ((-1 : ℤ) ^ (U \ W).card) • g W := by
  classical
  intro U
  have h1 : (∑ W ∈ U.powerset, ((-1 : ℤ) ^ (U \ W).card) • g W)
      = ∑ W ∈ U.powerset, ∑ V ∈ W.powerset, ((-1 : ℤ) ^ (U \ W).card) • h V := by
    apply Finset.sum_congr rfl
    intro W hW
    rw [hg W, Finset.smul_sum]
  have h2 := swap_double_sum (M := R) U
    (fun W V => ((-1 : ℤ) ^ (U \ W).card) • h V)
  have h3 : (∑ V ∈ U.powerset, ∑ W ∈ U.powerset.filter (fun W => V ⊆ W),
        ((-1 : ℤ) ^ (U \ W).card) • h V)
      = ∑ V ∈ U.powerset,
        (∑ W ∈ U.powerset.filter (fun W => V ⊆ W), ((-1 : ℤ) ^ (U \ W).card)) • h V := by
    apply Finset.sum_congr rfl
    intro V hV
    exact (Finset.sum_smul
      (f := fun W => ((-1 : ℤ) ^ (U \ W).card))
      (s := U.powerset.filter (fun W => V ⊆ W)) (x := h V)).symm
  have h4 : (∑ V ∈ U.powerset,
        (∑ W ∈ U.powerset.filter (fun W => V ⊆ W), ((-1 : ℤ) ^ (U \ W).card)) • h V)
      = ∑ V ∈ U.powerset, (if V = U then 1 else 0) • h V := by
    apply Finset.sum_congr rfl
    intro V hV
    have hVU : V ⊆ U := Finset.mem_powerset.mp hV
    rw [key_compl U V hVU]
    by_cases h : V = U
    · rw [if_pos h, if_pos h.symm]
      simp
    · rw [if_neg h, if_neg (fun huv => h huv.symm)]
      simp
  have h5 : (∑ V ∈ U.powerset, (if V = U then 1 else 0) • h V) = h U := by
    rw [Finset.sum_eq_single U]
    · simp
    · intro V hV hVU
      simp [hVU]
    · intro hnot
      exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl U)) hnot
  calc h U = ∑ V ∈ U.powerset, (if V = U then 1 else 0) • h V := h5.symm
    _ = ∑ V ∈ U.powerset,
        (∑ W ∈ U.powerset.filter (fun W => V ⊆ W), ((-1 : ℤ) ^ (U \ W).card)) • h V := h4.symm
    _ = ∑ V ∈ U.powerset, ∑ W ∈ U.powerset.filter (fun W => V ⊆ W),
        ((-1 : ℤ) ^ (U \ W).card) • h V := h3.symm
    _ = ∑ W ∈ U.powerset, ∑ V ∈ W.powerset, ((-1 : ℤ) ^ (U \ W).card) • h V := h2.symm
    _ = ∑ W ∈ U.powerset, ((-1 : ℤ) ^ (U \ W).card) • g W := h1.symm

private lemma mobius_backward {β R : Type*} [Fintype β] [DecidableEq β] [AddCommGroup R]
    (g h : Finset β → R)
    (hh : ∀ U, h U = ∑ W ∈ U.powerset, ((-1 : ℤ) ^ (U \ W).card) • g W) :
    ∀ W, g W = ∑ U ∈ W.powerset, h U := by
  classical
  intro W
  have h1 : (∑ U ∈ W.powerset, h U)
      = ∑ U ∈ W.powerset, ∑ V ∈ U.powerset, ((-1 : ℤ) ^ (U \ V).card) • g V := by
    apply Finset.sum_congr rfl
    intro U hU
    rw [hh U]
  have h2 := swap_double_sum (M := R) W
    (fun U V => ((-1 : ℤ) ^ (U \ V).card) • g V)
  have h3 : (∑ V ∈ W.powerset, ∑ U ∈ W.powerset.filter (fun U => V ⊆ U),
        ((-1 : ℤ) ^ (U \ V).card) • g V)
      = ∑ V ∈ W.powerset,
        (∑ U ∈ W.powerset.filter (fun U => V ⊆ U), ((-1 : ℤ) ^ (U \ V).card)) • g V := by
    apply Finset.sum_congr rfl
    intro V hV
    exact (Finset.sum_smul
      (f := fun U => ((-1 : ℤ) ^ (U \ V).card))
      (s := W.powerset.filter (fun U => V ⊆ U)) (x := g V)).symm
  have h4 : (∑ V ∈ W.powerset,
        (∑ U ∈ W.powerset.filter (fun U => V ⊆ U), ((-1 : ℤ) ^ (U \ V).card)) • g V)
      = ∑ V ∈ W.powerset, (if V = W then 1 else 0) • g V := by
    apply Finset.sum_congr rfl
    intro V hV
    have hVW : V ⊆ W := Finset.mem_powerset.mp hV
    rw [key_sub W V hVW]
    by_cases h : V = W
    · rw [if_pos h, if_pos h.symm]
      simp
    · rw [if_neg h, if_neg (fun huv => h huv.symm)]
      simp
  have h5 : (∑ V ∈ W.powerset, (if V = W then 1 else 0) • g V) = g W := by
    rw [Finset.sum_eq_single W]
    · simp
    · intro V hV hVW
      simp [hVW]
    · intro hnot
      exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl W)) hnot
  calc g W = ∑ V ∈ W.powerset, (if V = W then 1 else 0) • g V := h5.symm
    _ = ∑ V ∈ W.powerset,
        (∑ U ∈ W.powerset.filter (fun U => V ⊆ U), ((-1 : ℤ) ^ (U \ V).card)) • g V := h4.symm
    _ = ∑ V ∈ W.powerset, ∑ U ∈ W.powerset.filter (fun U => V ⊆ U),
        ((-1 : ℤ) ^ (U \ V).card) • g V := h3.symm
    _ = ∑ U ∈ W.powerset, ∑ V ∈ U.powerset, ((-1 : ℤ) ^ (U \ V).card) • g V := h2.symm
    _ = ∑ U ∈ W.powerset, h U := h1.symm

/-- Möbius inversion on the subset lattice, with values in an abelian group. -/
theorem solution {β R : Type*} [Fintype β] [DecidableEq β] [AddCommGroup R]
    (g h : Finset β → R) :
    (∀ W, g W = ∑ U ∈ W.powerset, h U) ↔
      ∀ U, h U = ∑ W ∈ U.powerset, ((-1 : ℤ) ^ (U \ W).card) • g W :=
  ⟨mobius_forward g h, mobius_backward g h⟩
