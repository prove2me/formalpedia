-- Prove2me | solution 1 for NestedLogitVariants.Competitive.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:07:25.825537+00:00
-- url     : https://prove2.me/submissions/ce0756fa-c343-4915-986b-f800740637e8

import Definitions.Def_NestedLogitVariants_Competitive_Model
import Theorems.Thm_NestedLogitVariants_Competitive_optimal_of_v0_eq_zero
import Theorems.Thm_NestedLogitVariants_Competitive_insert_higher_revenue_optimal

open NestedLogitVariants.Competitive

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hfc : ∀ i, I.vnp i = 0) :
    ∃ S : ι → Finset (Fin n), IsOptimal I S ∧ ∀ i, ∃ j ≤ n, S i = nbr n j := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro S'
      have he : S' = (fun _ => ∅) := by
        funext i; ext j; exact Fin.elim0 j
      rw [he]
    · intro i
      exact ⟨0, le_rfl, by simp [nbr]⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  by_cases hv0 : I.v0 = 0
  · cases isEmpty_or_nonempty ι with
    | inl h =>
      letI := h
      refine ⟨fun _ => ∅, ?_, ?_⟩
      · intro S'
        have he : S' = (fun _ => ∅) := Subsingleton.elim _ _
        rw [he]
      · intro i; exact isEmptyElim i
    | inr h =>
      letI := h
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
        (fun l => I.r l ⟨0, hnpos⟩) Finset.univ_nonempty
      refine ⟨fun l => if l = i then nbr n 1 else ∅,
        NestedLogitVariants.Competitive.optimal_of_v0_eq_zero I hI hfc hv0 hnpos i
          (fun l => hi l (Finset.mem_univ l)), ?_⟩
      intro l
      by_cases hl : l = i
      · exact ⟨1, hnpos, by simp [hl]⟩
      · exact ⟨0, Nat.zero_le n, by simp [hl, nbr]⟩
  have hv0pos : 0 < I.v0 := lt_of_le_of_ne hI.v0_nonneg (Ne.symm hv0)
  obtain ⟨S0, _, hS0⟩ := Finset.exists_max_image (Finset.univ : Finset (ι → Finset (Fin n)))
    (revenue I) Finset.univ_nonempty
  have hopt0 : IsOptimal I S0 := fun S' => hS0 S' (Finset.mem_univ S')
  let O : Finset (ι → Finset (Fin n)) := Finset.univ.filter (IsOptimal I)
  have hO : O.Nonempty := ⟨S0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hopt0⟩⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image O (fun T => ∑ i, (T i).card) hO
  have hopt : IsOptimal I S := (Finset.mem_filter.mp hS).2
  have hclosed : ∀ i j, j ∈ S i → ∀ k, k < j → k ∈ S i := by
    intro i j hj k hkj
    by_contra hk
    let T := Function.update S i (insert k (S i))
    have hoptT : IsOptimal I T := NestedLogitVariants.Competitive.insert_higher_revenue_optimal
      I hI hγ hfc hv0pos S hopt i j k hj hk hkj
    have hT : T ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoptT⟩
    have hcard : (∑ l, (S l).card) < ∑ l, (T l).card := by
      apply Finset.sum_lt_sum
      · intro l _
        by_cases hl : l = i
        · subst l
          simp only [T, Function.update_self]
          exact Finset.card_le_card (Finset.subset_insert _ _)
        · simp [T, hl]
      · exact ⟨i, Finset.mem_univ _, by simp [T, Finset.card_insert_of_notMem hk]⟩
    exact (not_lt_of_ge (hmax T hT)) hcard
  refine ⟨S, hopt, ?_⟩
  intro i
  by_cases hne : (S i).Nonempty
  · let m := (S i).max' hne
    have hm : m ∈ S i := Finset.max'_mem _ hne
    refine ⟨m.val + 1, m.isLt, ?_⟩
    ext k
    simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hk
      have hkm : k ≤ m := Finset.le_max' _ _ hk
      have := Fin.le_def.mp hkm
      omega
    · intro hk
      have hkm : k ≤ m := Fin.le_def.mpr (by omega)
      rcases lt_or_eq_of_le hkm with hlt | rfl
      · exact hclosed i m hm k hlt
      · exact hm
  · exact ⟨0, Nat.zero_le n, by simp [Finset.not_nonempty_iff_eq_empty.mp hne, nbr]⟩

#print axioms solution
