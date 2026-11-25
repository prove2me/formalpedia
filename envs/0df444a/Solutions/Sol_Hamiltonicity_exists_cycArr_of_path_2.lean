-- Prove2me | solution 2 for Hamiltonicity.exists_cycArr_of_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:51:52.655307+00:00
-- url     : https://prove2.me/submissions/39f7db71-da9b-49bd-bd3f-9bdacf98d1f5

module
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Definitions.Def_MengerHamilton_ClosureAux
public import Theorems.Thm_Hamiltonicity_CycArr_of_fun
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : ℕ → V) (hn : 3 ≤ Fintype.card V)
    (hinj : ∀ i j, i < Fintype.card V → j < Fintype.card V → x i = x j → i = j)
    (hadj : ∀ i, i + 1 < Fintype.card V → G.Adj (x i) (x (i + 1)))
    (hdeg : Fintype.card V ≤ G.degree (x 0) + G.degree (x (Fintype.card V - 1))) :
    ∃ g, CycArr G (Fintype.card V) g := by
  classical
  set n := Fintype.card V with hn_def
  have hsurj : ∀ w, ∃ j < n, x j = w := by
    have himg : (Finset.range n).image x = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      exact hinj i j (by simpa using hi) (by simpa using hj) hij
    intro w
    have : w ∈ (Finset.range n).image x := himg ▸ Finset.mem_univ w
    simpa using this
  set I := (Finset.range (n - 1)).filter (fun i => G.Adj (x 0) (x (i + 1))) with hI_def
  set J := (Finset.range (n - 1)).filter (fun i => G.Adj (x (n - 1)) (x i)) with hJ_def
  have hI : I.card = G.degree (x 0) := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset (x 0) = I.image (fun i => x (i + 1)) := by
      ext w
      simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range, I]
      constructor
      · intro hw
        obtain ⟨j, hj, rfl⟩ := hsurj w
        have hj0 : j ≠ 0 := by rintro rfl; exact G.irrefl hw
        refine ⟨j - 1, ⟨by omega, ?_⟩, ?_⟩
        · rwa [Nat.sub_add_cancel (by omega)]
        · rw [Nat.sub_add_cancel (by omega)]
      · rintro ⟨i, ⟨_, hi⟩, rfl⟩
        exact hi
    rw [this, Finset.card_image_of_injOn]
    intro i hi j hj hij
    have hi' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
    have hj' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
    have := hinj _ _ (by omega) (by omega) hij
    omega
  have hJ : J.card = G.degree (x (n - 1)) := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset (x (n - 1)) = J.image x := by
      ext w
      simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range, J]
      constructor
      · intro hw
        obtain ⟨j, hj, rfl⟩ := hsurj w
        have hj0 : j ≠ n - 1 := by rintro rfl; exact G.irrefl hw
        exact ⟨j, ⟨by omega, hw⟩, rfl⟩
      · rintro ⟨i, ⟨_, hi⟩, rfl⟩
        exact hi
    rw [this, Finset.card_image_of_injOn]
    intro i hi j hj hij
    have hi' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
    have hj' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
    exact hinj _ _ (by omega) (by omega) hij
  have hex : ∃ i, i < n - 1 ∧ G.Adj (x 0) (x (i + 1)) ∧ G.Adj (x (n - 1)) (x i) := by
    by_contra hne
    push Not at hne
    have hdisj : Disjoint I J := by
      rw [Finset.disjoint_left]
      intro i hiI hiJ
      simp only [I, J, Finset.mem_filter, Finset.mem_range] at hiI hiJ
      exact hne i hiI.1 hiI.2 hiJ.2
    have h1 := Finset.card_union_of_disjoint hdisj
    have hsub : I ∪ J ⊆ Finset.range (n - 1) :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_range] at h2
    omega
  obtain ⟨i, hi, hu, hv⟩ := hex
  let h : ℕ → V := fun j => if j ≤ i then x j else if j < n then x (n + i - j) else x 0
  refine ⟨_, CycArr.of_fun (h := h) hn ?_ ?_ ?_⟩
  · intro a b ha hb hab
    have key : ∀ j, j < n → h j = x (if j ≤ i then j else n + i - j) := by
      intro j hj
      simp only [h]
      split_ifs <;> rfl
    rw [key a ha, key b hb] at hab
    have := hinj _ _ (by split_ifs <;> omega) (by split_ifs <;> omega) hab
    split_ifs at this <;> omega
  · intro j hj
    rcases lt_trichotomy j i with hji | rfl | hji
    · have e1 : h j = x j := if_pos hji.le
      have e2 : h (j + 1) = x (j + 1) := if_pos hji
      rw [e1, e2]
      exact hadj j (by omega)
    · have e1 : h j = x j := if_pos le_rfl
      have e2 : h (j + 1) = x (n - 1) := by
        simp only [h]
        rw [if_neg (by omega), if_pos (by omega)]
        congr 1; omega
      rw [e1, e2]
      exact hv.symm
    · by_cases hjn : j + 1 < n
      · have e1 : h j = x (n + i - j) := by
          simp only [h]
          rw [if_neg (by omega), if_pos (by omega)]
        have e2 : h (j + 1) = x (n + i - j - 1) := by
          simp only [h]
          rw [if_neg (by omega), if_pos (by omega)]
          congr 1
        rw [e1, e2]
        have := hadj (n + i - j - 1) (by omega)
        rw [show n + i - j - 1 + 1 = n + i - j by omega] at this
        exact this.symm
      · have e1 : h j = x (i + 1) := by
          simp only [h]
          rw [if_neg (by omega), if_pos (by omega)]
          congr 1; omega
        have e2 : h (j + 1) = x 0 := by
          simp only [h]
          rw [if_neg (by omega), if_neg (by omega)]
        rw [e1, e2]
        exact hu.symm
  · simp only [h]
    rw [if_neg (by omega), if_neg (by omega), if_pos (Nat.zero_le _)]
end Hamiltonicity
