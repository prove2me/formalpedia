-- Prove2me | solution 1 for MNLBandit.UCB.lemma_4_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:21:53.096629+00:00
-- url     : https://prove2.me/submissions/e8a69ae9-4755-4c14-8838-43f2e2bf11ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1
import Theorems.Thm_MNLBandit_UCB_lemma_4_1
import Theorems.Thm_MNLBandit_UCB_lemma_A_4

open ChoiceCDLP.MNL MNLBandit.UCB

namespace MNLLemma41Aux

lemma histProb_nonneg {N T : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N)
    (h : History N T) : 0 ≤ histProb v π h := by
  unfold histProb
  apply Finset.prod_nonneg
  intro t _
  have hden : 0 < 1 + ∑ j ∈ offered π h t, v j :=
    by have := Finset.sum_nonneg (fun j (_ : j ∈ offered π h t) => hv0 j); linarith
  cases h t with
  | none => simp only [choiceProb]; positivity
  | some i =>
    simp only [choiceProb]
    split_ifs
    · exact div_nonneg (hv0 i) hden.le
    · exact le_refl 0

lemma probT_mono {N : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (E F : History N T → Prop) (hEF : ∀ h, E h → F h) :
    probT v π T E ≤ probT v π T F := by
  unfold probT
  apply Finset.sum_le_sum
  intro h _
  have := histProb_nonneg v hv0 π h
  by_cases hE : E h
  · rw [if_pos hE, if_pos (hEF h hE)]
  · rw [if_neg hE]; split_ifs <;> linarith

lemma probT_or {N : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (E F : History N T → Prop) :
    probT v π T (fun h => E h ∨ F h) ≤ probT v π T E + probT v π T F := by
  unfold probT
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h _
  have := histProb_nonneg v hv0 π h
  by_cases hE : E h
  · rw [if_pos (Or.inl hE), if_pos hE]; split_ifs <;> linarith
  · by_cases hF : F h
    · rw [if_pos (Or.inr hF), if_neg hE, if_pos hF]; linarith
    · rw [if_neg (by tauto), if_neg hE, if_neg hF]; simp

lemma sqrt_add_le' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have := Real.sq_sqrt ha; have := Real.sq_sqrt hb
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)


open scoped Classical in
lemma probT_exists {N : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (E : Fin N → History N T → Prop) :
    probT v π T (fun h => ∃ j, E j h) ≤ ∑ j, probT v π T (E j) := by
  unfold probT
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro h _
  have hx := histProb_nonneg v hv0 π h
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      0 ≤ (if E j h then histProb v π h else 0) := by
    intro j _; split_ifs <;> linarith
  by_cases hE : ∃ j, E j h
  · obtain ⟨j0, hj0⟩ := hE
    rw [if_pos ⟨j0, hj0⟩]
    have := Finset.single_le_sum hnn (Finset.mem_univ j0)
    rw [if_pos hj0] at this
    exact this
  · rw [if_neg hE]; exact Finset.sum_nonneg hnn

lemma sum_const_bound (N ℓ : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∑ _j : Fin N, c / (N * ℓ) ≤ c / ℓ := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp; positivity
  · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
    rcases Nat.eq_zero_or_pos ℓ with hl | hl
    · subst hl; simp
    · have hl' : (0 : ℝ) < ℓ := by exact_mod_cast hl
      rw [le_div_iff₀ hl']
      field_simp
      exact le_refl _

lemma vUCB_ge_one_of_zero {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (j : Fin N) (ℓ : ℕ)
    (h0 : Tcount r sel h j ℓ = 0) : vUCB r sel h j ℓ = 1 := by
  simp only [vUCB, vUCBL]
  have : TcountL (pastUpTo r sel h ℓ) j = 0 := h0
  simp [this]

end MNLLemma41Aux

open MNLLemma41Aux in
theorem solution {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧
        (∀ i ∈ nextSet r sel h ℓ, 1 ≤ Tcount r sel h i ℓ) ∧
        ¬ ((1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
              (mnlObjective (fun j => vUCB r sel h j ℓ) r 1 (nextSet r sel h ℓ)
                - mnlObjective v r 1 (nextSet r sel h ℓ)) ≤
            ∑ i ∈ nextSet r sel h ℓ,
              ((Real.sqrt 72 + Real.sqrt 24)
                  * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
                + 144 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)))
      ≤ 13 / ℓ := by
  set B : History N T → Fin N → ℝ := fun h i =>
    (Real.sqrt 72 + Real.sqrt 24)
        * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
      + 144 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ with hB
  set E1 : Fin N → History N T → Prop := fun j h =>
    ℓ ≤ epochsDone r sel h ∧ vUCB r sel h j ℓ < v j with hE1
  set E2 : Fin N → History N T → Prop := fun j h =>
    ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h j ℓ ∧ vUCB r sel h j ℓ - v j > B h j with hE2
  have hsub : ∀ h : History N T, (ℓ ≤ epochsDone r sel h ∧
        (∀ i ∈ nextSet r sel h ℓ, 1 ≤ Tcount r sel h i ℓ) ∧
        ¬ ((1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
              (mnlObjective (fun j => vUCB r sel h j ℓ) r 1 (nextSet r sel h ℓ)
                - mnlObjective v r 1 (nextSet r sel h ℓ)) ≤
            ∑ i ∈ nextSet r sel h ℓ, B h i)) →
      (∃ j, E1 j h) ∨ (∃ j, E2 j h) := by
    intro h ⟨hl, hT, hnot⟩
    by_contra hall
    simp only [not_or, not_exists, hE1, hE2, not_and, not_lt, gt_iff_lt] at hall
    obtain ⟨h1, h2⟩ := hall
    apply hnot
    set S := nextSet r sel h ℓ with hS
    set u : Fin N → ℝ := fun j => vUCB r sel h j ℓ with hu
    have hvu : ∀ i ∈ S, v i ≤ u i := fun i _ => h1 i hl
    have hA4 := lemma_A_4 r hr v u S (fun i _ => hv0 i) hvu
    have hV : 0 < 1 + ∑ j ∈ S, v j := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ S) => hv0 j); linarith
    have step1 : (1 + ∑ j ∈ S, v j) * (mnlObjective u r 1 S - mnlObjective v r 1 S) ≤
        ∑ j ∈ S, (u j - v j) := by
      have := mul_le_mul_of_nonneg_left hA4 hV.le
      rwa [mul_div_cancel₀ _ hV.ne'] at this
    refine step1.trans (Finset.sum_le_sum ?_)
    intro i hi
    exact h2 i hl (hT i hi)
  calc _ ≤ probT v (alg1 r sel) T (fun h => (∃ j, E1 j h) ∨ (∃ j, E2 j h)) :=
        probT_mono v hv0 _ T _ _ hsub
    _ ≤ probT v (alg1 r sel) T (fun h => ∃ j, E1 j h) +
          probT v (alg1 r sel) T (fun h => ∃ j, E2 j h) := probT_or v hv0 _ T _ _
    _ ≤ (∑ j, probT v (alg1 r sel) T (E1 j)) + ∑ j, probT v (alg1 r sel) T (E2 j) :=
        add_le_add (probT_exists v hv0 _ T E1) (probT_exists v hv0 _ T E2)
    _ ≤ (∑ _j : Fin N, (6 : ℝ) / (N * ℓ)) + ∑ _j : Fin N, (7 : ℝ) / (N * ℓ) := by
        apply add_le_add
        · apply Finset.sum_le_sum; intro j _
          exact (lemma_4_1 v r 𝒮 sel hTU hdc hne hsel hv0 hv1 hr T ℓ hℓ j).1
        · apply Finset.sum_le_sum; intro j _
          exact (lemma_4_1 v r 𝒮 sel hTU hdc hne hsel hv0 hv1 hr T ℓ hℓ j).2
    _ ≤ 6 / ℓ + 7 / ℓ := add_le_add (sum_const_bound N ℓ 6 (by norm_num))
          (sum_const_bound N ℓ 7 (by norm_num))
    _ = 13 / ℓ := by ring
