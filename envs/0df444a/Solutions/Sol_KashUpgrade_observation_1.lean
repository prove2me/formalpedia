-- Prove2me | solution 1 for KashUpgrade.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:00:55.605376+00:00
-- url     : https://prove2.me/submissions/d8f747ed-fc3c-4460-bacd-cf500c33e3b4

import Mathlib
import Definitions.Def_KashUpgrade_IsUpgradeBoundAt
import Definitions.Def_KashUpgrade_sliceRevenue

set_option autoImplicit false

open KashUpgrade

namespace KashUpgrade.Obs1Proof

theorem smono (S : Schedule) (a : ℕ) : ∀ b, a ≤ b → IsIntroduced S b → S.s a ≤ S.s b := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ b hab ih =>
    intro hb
    have hb' : IsIntroduced S b := by
      unfold IsIntroduced at hb ⊢
      exact le_trans (by exact_mod_cast Nat.le_succ b) hb
    exact (ih hb').trans (S.s_lt b hb).le

theorem intro_mono (S : Schedule) {a b : ℕ} (hab : a ≤ b) (hb : IsIntroduced S b) :
    IsIntroduced S a := by
  unfold IsIntroduced at hb ⊢
  exact le_trans (by exact_mod_cast hab) hb

theorem key (S : Schedule) (x x' : ℕ → ℕ → ℝ) (c θ : ℝ) {d j n : ℕ} (hd : 2 ≤ d) (hj : 1 ≤ j)
    (hjS : IsIntroduced S j) (hn : IsUpgradeBoundAt S d j n)
    (h₀ : ∀ i, 1 ≤ i → i ≤ j → x i 0 = x' i 0)
    (h₁ : ∀ i, 1 ≤ i → i ≤ n → x (j + i) i = x' (j + i) i) :
    ∀ k t, k + 1 ≤ d → k + 1 ≤ t + 1 → S.s j ≤ t + 1 - (k + 1) →
      (IsIntroduced S (j + 1) → t + 1 - (k + 1) < S.s (j + 1)) →
      customerState S x c (k + 1) t θ = customerState S x' c (k + 1) t θ ∧
      (((customerState S x c (k + 1) t θ).1 ≤ j ∧ (customerState S x c (k + 1) t θ).2 = 0) ∨
       ((customerState S x c (k + 1) t θ).1 = j + (customerState S x c (k + 1) t θ).2 ∧
        1 ≤ (customerState S x c (k + 1) t θ).2 ∧ (customerState S x c (k + 1) t θ).2 ≤ n)) := by
  have hle : ∀ i t, IsIntroduced S i → S.s i ≤ t → (IsIntroduced S (j + 1) → t < S.s (j + 1)) →
      i ≤ j := by
    intro i t hi hit hlt
    by_contra hc
    push Not at hc
    have hj1 : IsIntroduced S (j + 1) := intro_mono S hc hi
    have := smono S (j + 1) i hc hi
    have := hlt hj1
    omega
  have hP0 : ∀ i t, IsIntroduced S i → S.s i ≤ t → (IsIntroduced S (j + 1) → t < S.s (j + 1)) →
      classPrice x i 0 = classPrice x' i 0 := by
    intro i t hi hit hlt
    have := hle i t hi hit hlt
    unfold classPrice
    split_ifs with h
    · rfl
    · exact h₀ i (by omega) this
  intro k
  induction k with
  | zero =>
    intro t hd1 ht hsj hlt
    have hlt' : IsIntroduced S (j + 1) → t < S.s (j + 1) := by
      intro h
      have := hlt h
      omega
    have hnc : newCustomerChoice S x t θ = newCustomerChoice S x' t θ := by
      unfold newCustomerChoice
      congr 1
      ext i
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, h2, fun i' h1' h2' => ?_⟩
        rw [← hP0 i' t h1' h2' hlt', ← hP0 i t h1 h2 hlt']
        exact h3 i' h1' h2'
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, h2, fun i' h1' h2' => ?_⟩
        rw [hP0 i' t h1' h2' hlt', hP0 i t h1 h2 hlt']
        exact h3 i' h1' h2'
    have hbound : newCustomerChoice S x t θ ≤ j := by
      unfold newCustomerChoice
      apply csSup_le'
      rintro i ⟨h1, h2, -⟩
      exact hle i t h1 h2 hlt'
    rw [customerState, customerState]
    exact ⟨by rw [hnc], Or.inl ⟨hbound, rfl⟩⟩
  | succ k ih =>
    intro t hd1 ht hsj hlt
    have hs1 : S.s 1 ≤ S.s j := smono S 1 j hj hjS
    have ht1 : ¬ t ≤ S.s 1 := by omega
    obtain ⟨hEq, hinv⟩ := ih (t - 1) (by omega) (by omega) (by omega)
      (fun h => by have := hlt h; omega)
    rw [customerState, customerState, if_neg ht1, if_neg ht1]
    dsimp only
    rw [← hEq]
    generalize customerState S x c (k + 1) (t - 1) θ = P at hinv ⊢
    obtain ⟨q, m⟩ := P
    simp only at hinv ⊢
    have hprices : IsIntroduced S (q + 1) → S.s (q + 1) = t →
        classPrice x q m = classPrice x' q m ∧
          classPrice x (q + 1) (m + 1) = classPrice x' (q + 1) (m + 1) ∧
          m + 1 ≤ n ∧ q + 1 = j + (m + 1) := by
      intro hI hst
      rcases hinv with ⟨hq, rfl⟩ | ⟨rfl, hm1, hmn⟩
      · rcases Nat.lt_or_ge q j with hqj | hqj
        · exfalso
          have := smono S (q + 1) j (by omega) hjS
          omega
        · have hqj' : q = j := le_antisymm hq hqj
          rw [hqj'] at hI ⊢
          have h1n : 1 ≤ n := hn 1 le_rfl hI (by omega)
          refine ⟨?_, ?_, by omega, by omega⟩
          · unfold classPrice
            rw [if_neg (by omega), if_neg (by omega)]
            exact h₀ j hj le_rfl
          · unfold classPrice
            rw [if_neg (by omega), if_neg (by omega)]
            exact h₁ 1 le_rfl h1n
      · have hI' : IsIntroduced S (j + 1) := intro_mono S (by omega) hI
        have := hlt hI'
        have hmn' : m + 1 ≤ n := hn (m + 1) (by omega) (by rw [← add_assoc]; exact hI)
          (by rw [← add_assoc, hst]; omega)
        refine ⟨?_, ?_, hmn', by omega⟩
        · unfold classPrice
          rw [if_neg (by omega), if_neg (by omega)]
          exact h₁ m hm1 hmn
        · unfold classPrice
          rw [if_neg (by omega), if_neg (by omega)]
          have := h₁ (m + 1) (by omega) hmn'
          rw [← add_assoc] at this
          exact this
    by_cases hg : IsIntroduced S (q + 1) ∧ S.s (q + 1) = t ∧
        θ * S.s q - classPrice x q m ≤ θ * S.s (q + 1) - classPrice x (q + 1) (m + 1) - c
    · obtain ⟨hI, hst, hc⟩ := hg
      obtain ⟨e1, e2, hmn', hq'⟩ := hprices hI hst
      rw [if_pos ⟨hI, hst, hc⟩, if_pos ⟨hI, hst, by rw [← e1, ← e2]; exact hc⟩]
      exact ⟨rfl, Or.inr ⟨by simpa using hq', by omega, hmn'⟩⟩
    · have hg' : ¬ (IsIntroduced S (q + 1) ∧ S.s (q + 1) = t ∧
          θ * S.s q - classPrice x' q m ≤
            θ * S.s (q + 1) - classPrice x' (q + 1) (m + 1) - c) := by
        rintro ⟨hI, hst, hc⟩
        obtain ⟨e1, e2, -, -⟩ := hprices hI hst
        exact hg ⟨hI, hst, by rw [e1, e2]; exact hc⟩
      rw [if_neg hg, if_neg hg']
      exact ⟨rfl, hinv⟩

end KashUpgrade.Obs1Proof

open KashUpgrade.Obs1Proof in
theorem solution (f : ℝ → ℝ) (S : Schedule) {d : ℕ} (c δ : ℝ) (hd : 2 ≤ d) {j n : ℕ} (hj : 1 ≤ j) (hjS : IsIntroduced S j) (hn : IsUpgradeBoundAt S d j n) (x x' : ℕ → ℕ → ℝ) (h₀ : ∀ i, 1 ≤ i → i ≤ j → x i 0 = x' i 0) (h₁ : ∀ i, 1 ≤ i → i ≤ n → x (j + i) i = x' (j + i) i) : sliceRevenue f S d c δ j x = sliceRevenue f S d c δ j x' := by
  unfold sliceRevenue
  congr 1
  funext t
  congr 1
  congr 1
  funext θ
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  simp only [sliceAges, Finset.mem_Icc] at hℓ
  obtain ⟨hlo, hhi⟩ := hℓ
  have h1 : 1 ≤ ℓ := by split_ifs at hlo <;> omega
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hlt : IsIntroduced S (j + 1) → t + 1 - (k + 1) < S.s (j + 1) := by
    intro hI
    rw [if_pos hI] at hlo
    omega
  obtain ⟨hEq, hinv⟩ := key S x x' c θ hd hj hjS hn h₀ h₁ k t (by omega) (by omega) (by omega) hlt
  rw [← hEq]
  generalize customerState S x c (k + 1) t θ = P at hinv ⊢
  obtain ⟨q, m⟩ := P
  simp only at hinv ⊢
  rcases hinv with ⟨hq, rfl⟩ | ⟨rfl, hm1, hmn⟩
  · unfold classPrice
    split_ifs with h
    · rfl
    · exact h₀ q (by omega) hq
  · unfold classPrice
    rw [if_neg (by omega), if_neg (by omega)]
    exact h₁ m hm1 hmn
