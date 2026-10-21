-- Prove2me | solution 1 for GraphAlignment.Possible.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:57:39.638209+00:00
-- url     : https://prove2.me/submissions/29c30fe9-426f-4c4f-90c6-483bf0feb780

import Mathlib
import Definitions.Def_GraphAlignment_Possible_PermutationSets

set_option autoImplicit false

open GraphAlignment.Possible

theorem solution (n : ℕ) (hn : 0 < n) (p : Equiv.Perm (Fin n)) :
    let m : ℕ := numFixed p
    let ε : ℝ := (m : ℝ) / n
    ((S12 p).card : ℝ) ≤ n * (1 - ε) ∧
      ((Sbar22 p).card : ℝ) ≤ (n.choose 2 : ℝ) - (m.choose 2 : ℝ) ∧
      (n.choose 2 : ℝ) - (m.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 * (1 - ε ^ 2) := by
  intro m ε
  set F : Finset (Fin n) := Finset.univ.filter fun i => p i = i with hF
  have hm : m = F.card := rfl
  have hmn : m ≤ n := by
    rw [hm]; simpa using Finset.card_le_univ F
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  -- non-fixed points count
  have hNF : (Finset.univ.filter fun i : Fin n => p i ≠ i).card = n - m := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => p i = i)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have hm' : m = (Finset.univ.filter fun i : Fin n => p i = i).card := rfl
    simp only [ne_eq]
    omega
  have h1 : (S12 p).card ≤ n - m := by
    rw [← hNF]
    apply Finset.card_le_card_of_injOn (fun x => x.1)
    · intro x hx
      simp only [S12, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
      simp [hx.2.1]
    · intro x hx y hy hxy
      simp only [S12, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      have : x.1 = y.1 := hxy
      exact Prod.ext this (by rw [← hx.2.2.1, ← hy.2.2.1, this])
  have hsub : (Sbar22 p) ⊆ (Finset.univ.offDiag.image Sym2.mk.uncurry) \ (F.offDiag.image Sym2.mk.uncurry) := by
    intro e he
    simp only [Sbar22, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · induction e using Sym2.ind with
      | _ a b =>
        rw [Finset.mem_image]
        exact ⟨(a, b), by simpa [Finset.mem_offDiag, Sym2.mk_isDiag_iff] using he.1, rfl⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
      simp only [Finset.mem_offDiag, hF, Finset.mem_filter, Finset.mem_univ, true_and] at hab
      apply he.2
      simp [Sym2.map_pair_eq, hab.1, hab.2.1]
  have hsub2 : (F.offDiag.image Sym2.mk.uncurry) ⊆ (Finset.univ.offDiag.image Sym2.mk.uncurry) := by
    apply Finset.image_subset_image
    apply Finset.offDiag_mono
    exact Finset.subset_univ _
  have h2 : (Sbar22 p).card ≤ n.choose 2 - m.choose 2 := by
    calc (Sbar22 p).card ≤ _ := Finset.card_le_card hsub
      _ = n.choose 2 - m.choose 2 := by
        rw [Finset.card_sdiff_of_subset hsub2, Sym2.card_image_offDiag, Sym2.card_image_offDiag,
          hm]
        simp
  have hch : m.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hmn
  refine ⟨?_, ?_, ?_⟩
  · have : ((S12 p).card : ℝ) ≤ ((n - m : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub hmn] at this
    have e : (n : ℝ) * (1 - ε) = n - m := by
      simp only [ε]; field_simp
    rw [e]; exact this
  · have : ((Sbar22 p).card : ℝ) ≤ ((n.choose 2 - m.choose 2 : ℕ) : ℝ) := by exact_mod_cast h2
    rwa [Nat.cast_sub hch] at this
  · have e1 : (n.choose 2 : ℝ) = n * (n - 1) / 2 := by
      rw [Nat.cast_choose_two]
    have e2 : (m.choose 2 : ℝ) = m * (m - 1) / 2 := by
      rw [Nat.cast_choose_two]
    have e : (n : ℝ) ^ 2 / 2 * (1 - ε ^ 2) = ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) / 2 := by
      simp only [ε]; field_simp
    rw [e, e1, e2]
    nlinarith
