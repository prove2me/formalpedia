-- Prove2me | solution 1 for MultiStoreAssort.SQR.theorem4_nested_revenue_ordered
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:33:47.899231+00:00
-- url     : https://prove2.me/submissions/56e64629-f8dc-4965-8c5c-e7d7c16b7eed

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model
import Theorems.Thm_MultiStoreAssort_SQR_propositionB2_nested_revenue_ordered
import Theorems.Thm_MultiStoreAssort_SQR_step3_case1_replace_stilde
import Theorems.Thm_MultiStoreAssort_SQR_step3_case2_add_product

open MultiStoreAssort.SQR

theorem solution {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hn : 0 < n) (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) (St : Finset (Fin n)) (hSt : MultiStoreAssort.SMR.IsStilde r v St) :
    ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧
      (∀ i j, i ≤ j → j ≠ Fin.last (M + 1) → S i ⊆ S j) ∧
      S (Fin.last M).castSucc ⊆ St ∧ St ⊆ S (Fin.last (M + 1)) ∧
      ∀ i, MultiStoreAssort.SMR.IsRevenueOrdered (S i) := by
  classical
  -- basic facts on revenue-ordered sets
  have hcard : ∀ A : Finset (Fin n), MultiStoreAssort.SMR.IsRevenueOrdered A →
      A = MultiStoreAssort.SMR.prefixSet n A.card ∧ A.card ≤ n := by
    rintro A ⟨j, -, hjn, rfl⟩
    have : (MultiStoreAssort.SMR.prefixSet n j).card = j := by
      unfold MultiStoreAssort.SMR.prefixSet
      rw [Fin.card_filter_val_lt]; omega
    rw [this]; exact ⟨rfl, hjn⟩
  have hcomp : ∀ A B : Finset (Fin n), MultiStoreAssort.SMR.IsRevenueOrdered A →
      MultiStoreAssort.SMR.IsRevenueOrdered B → A ⊆ B ∨ B ⊆ A := by
    rintro A B ⟨a, -, -, rfl⟩ ⟨b, -, -, rfl⟩
    rcases le_total a b with h | h
    · left; intro x; simp [MultiStoreAssort.SMR.prefixSet]; omega
    · right; intro x; simp [MultiStoreAssort.SMR.prefixSet]; omega
  have hStro : MultiStoreAssort.SMR.IsRevenueOrdered St := hSt.1
  have hlastne : (Fin.last M).castSucc ≠ Fin.last (M + 1) := by
    intro h; have := congrArg Fin.val h; simp at this
  obtain ⟨S0, hopt0, hch0, hro0⟩ :=
    propositionB2_nested_revenue_ordered lam r v c cs hn hlam hlam1 hr hrpos hv hcii hsw hmin hmono
  by_cases hex : ∃ i : Fin (M + 2), i ≠ Fin.last (M + 1) ∧ St ⊂ S0 i
  · -- Case 1
    have hP : ∃ K : ℕ, ∃ h : K < M + 2, St ⊂ S0 ⟨K, h⟩ := by
      obtain ⟨i, -, hi⟩ := hex; exact ⟨i.val, i.isLt, hi⟩
    let K := Nat.find hP
    have hKspec : ∃ h : K < M + 2, St ⊂ S0 ⟨K, h⟩ := Nat.find_spec hP
    have hKmin : ∀ k < K, ¬ ∃ h : k < M + 2, St ⊂ S0 ⟨k, h⟩ := fun k hk => Nat.find_min hP hk
    have hKM : K ≤ M := by
      obtain ⟨i, hi1, hi2⟩ := hex
      have : K ≤ i.val := Nat.find_min' hP ⟨i.isLt, hi2⟩
      have : i.val ≠ M + 1 := fun h => hi1 (Fin.ext (by simpa using h))
      have := i.isLt; omega
    obtain ⟨hKlt, hKs⟩ := hKspec
    have hhigh : ∀ i : Fin (M + 2), K ≤ i.val → St ⊂ S0 i := by
      intro i hi
      exact Finset.ssubset_of_ssubset_of_subset hKs (hch0 _ _ (Fin.mk_le_of_le_val hi))
    have hlow : ∀ i : Fin (M + 2), i.val < K → S0 i ⊆ St := by
      intro i hi
      have hn' : ¬ St ⊂ S0 i := fun h => hKmin i.val hi ⟨i.isLt, h⟩
      rcases hcomp _ _ (hro0 i) hStro with h | h
      · exact h
      · have : St = S0 i := by
          by_contra hne; exact hn' (Finset.ssubset_iff_subset_ne.mpr ⟨h, hne⟩)
        rw [this]
    have hle := step3_case1_replace_stilde lam r v c cs hlam hlam1 hr hrpos hv hcii hsw hmin hmono
      St hSt S0 hch0 hro0 K hKM hlow hhigh
    refine ⟨fun i => if K ≤ i.val ∧ i ≠ Fin.last (M + 1) then St else S0 i, ?_, ?_, ?_, ?_, ?_⟩
    · intro S'; exact (hopt0 S').trans hle
    · intro i j hij hj
      by_cases hjK : K ≤ j.val
      · simp only [hjK, hj, ne_eq, not_false_eq_true, and_self, if_true]
        split_ifs with hi
        · exact le_rfl
        · have : i.val < K := by
            by_contra h'
            have hi' : i ≠ Fin.last (M + 1) := by
              intro h''; subst h''; exact hj (le_antisymm (Fin.le_last _) hij)
            exact hi ⟨by omega, hi'⟩
          exact hlow i this
      · have hiK : ¬ K ≤ i.val := fun h => hjK (le_trans h hij)
        simp only [hiK, hjK, false_and, if_false]
        exact hch0 i j hij
    · simp only
      split_ifs with h
      · exact le_rfl
      · have : (Fin.last M).castSucc.val < K := by
          by_contra h'; exact h ⟨by omega, hlastne⟩
        exact hlow _ this
    · have : ¬ (K ≤ (Fin.last (M + 1)).val ∧ Fin.last (M + 1) ≠ Fin.last (M + 1)) := by simp
      simp only [this, if_false]
      exact (hhigh _ (by simp; omega)).subset
    · intro i; simp only; split_ifs
      · exact hStro
      · exact hro0 i
  · -- Case 2: every non-last store is inside S̃; grow the last store.
    push Not at hex
    have hsubSt : ∀ i : Fin (M + 2), i ≠ Fin.last (M + 1) → S0 i ⊆ St := by
      intro i hi
      rcases hcomp _ _ (hro0 i) hStro with h | h
      · exact h
      · by_cases he : St = S0 i
        · rw [he]
        · exact absurd (Finset.ssubset_iff_subset_ne.mpr ⟨h, he⟩) (hex i hi)
    have key : ∀ d : ℕ, ∀ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S →
        (∀ i j, i ≤ j → S i ⊆ S j) → (∀ i, MultiStoreAssort.SMR.IsRevenueOrdered (S i)) →
        (∀ i, i ≠ Fin.last (M + 1) → S i ⊆ St) → St.card - (S (Fin.last (M + 1))).card = d →
        ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧
          (∀ i j, i ≤ j → j ≠ Fin.last (M + 1) → S i ⊆ S j) ∧
          S (Fin.last M).castSucc ⊆ St ∧ St ⊆ S (Fin.last (M + 1)) ∧
          ∀ i, MultiStoreAssort.SMR.IsRevenueOrdered (S i) := by
      intro d
      induction d with
      | zero =>
        intro S hopt hch hro hsub hd
        refine ⟨S, hopt, fun i j hij _ => hch i j hij, hsub _ hlastne, ?_, hro⟩
        rcases hcomp _ _ (hro (Fin.last (M + 1))) hStro with h | h
        · by_contra hne
          have hss : S (Fin.last (M + 1)) ⊂ St :=
            Finset.ssubset_iff_subset_ne.mpr ⟨h, fun he => hne (he ▸ le_rfl)⟩
          have := Finset.card_lt_card hss; omega
        · exact h
      | succ e ih =>
        intro S hopt hch hro hsub hd
        by_cases hStS : St ⊆ S (Fin.last (M + 1))
        · exact ⟨S, hopt, fun i j hij _ => hch i j hij, hsub _ hlastne, hStS, hro⟩
        have hss : S (Fin.last (M + 1)) ⊂ St := by
          rcases hcomp _ _ (hro (Fin.last (M + 1))) hStro with h | h
          · exact Finset.ssubset_iff_subset_ne.mpr ⟨h, fun he => hStS (he ▸ le_rfl)⟩
          · exact absurd h hStS
        have hclt := Finset.card_lt_card hss
        have hStn : St.card ≤ n := by simpa using Finset.card_le_univ St
        set L := S (Fin.last (M + 1)) with hL
        have hjlt : L.card < n := by omega
        let j : Fin n := ⟨L.card, hjlt⟩
        have hstep := step3_case2_add_product lam r v c cs hlam hlam1 hr hrpos hv hcii hsw hmin
          hmono St hSt S hch hro hss j rfl
        have hmemL : ∀ x : Fin n, x ∈ L ↔ x.val < L.card := by
          obtain ⟨hLeq, -⟩ := hcard L (hro _)
          intro x
          conv_lhs => rw [hLeq]
          simp [MultiStoreAssort.SMR.prefixSet]
        have hins : insert j L = MultiStoreAssort.SMR.prefixSet n (L.card + 1) := by
          ext x
          rw [Finset.mem_insert, hmemL]
          simp only [MultiStoreAssort.SMR.prefixSet, Finset.mem_filter, Finset.mem_univ,
            true_and, Fin.ext_iff, j]
          omega
        have hjL : j ∉ L := by
          rw [hmemL]; simp [j]
        apply ih (Function.update S (Fin.last (M + 1)) (insert j L))
        · intro S'; exact (hopt S').trans hstep
        · intro i k hik
          by_cases hk : k = Fin.last (M + 1)
          · subst hk
            rw [Function.update_self]
            by_cases hi : i = Fin.last (M + 1)
            · subst hi; rw [Function.update_self]
            · rw [Function.update_of_ne hi]
              exact (hch i _ hik).trans (Finset.subset_insert _ _)
          · have hi : i ≠ Fin.last (M + 1) := by
              intro h; subst h; exact hk (le_antisymm (Fin.le_last _) hik)
            rw [Function.update_of_ne hk, Function.update_of_ne hi]
            exact hch i k hik
        · intro i
          by_cases hi : i = Fin.last (M + 1)
          · subst hi; rw [Function.update_self, hins]
            exact ⟨L.card + 1, by omega, by omega, rfl⟩
          · rw [Function.update_of_ne hi]; exact hro i
        · intro i hi; rw [Function.update_of_ne hi]; exact hsub i hi
        · rw [Function.update_self, Finset.card_insert_of_notMem hjL]; omega
    exact key _ S0 hopt0 hch0 hro0 hsubSt rfl
