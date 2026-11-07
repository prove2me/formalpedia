-- Prove2me | solution 1 for MNLBandit.UCB.lemma_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:20:59.88626+00:00
-- url     : https://prove2.me/submissions/27c0312c-ec11-429d-b5e0-0a93a102fe28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1
import Theorems.Thm_MNLBandit_UCB_lemma_4_1
import Theorems.Thm_MNLBandit_UCB_lemma_A_3

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
    (Sstar : Finset (Fin N)) (hSstar : Sstar ∈ 𝒮)
    (hopt : mnlObjective v r 1 Sstar = optRevenue v r 𝒮 hne)
    (hpos : ∀ j ∈ Sstar, 0 < v j)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧
        ¬ (mnlObjective (fun j => vUCB r sel h j ℓ) r 1 (nextSet r sel h ℓ) ≥
              mnlObjective (fun j => vUCB r sel h j ℓ) r 1 Sstar ∧
            mnlObjective (fun j => vUCB r sel h j ℓ) r 1 Sstar ≥ mnlObjective v r 1 Sstar))
      ≤ 6 / ℓ := by
  have hopt' : ∀ Q ∈ 𝒮, mnlObjective v r 1 Q ≤ mnlObjective v r 1 Sstar := by
    intro Q hQ
    rw [hopt]
    exact Finset.le_sup' (fun S => mnlObjective v r 1 S) hQ
  have hsub : ∀ h : History N T, (ℓ ≤ epochsDone r sel h ∧
        ¬ (mnlObjective (fun j => vUCB r sel h j ℓ) r 1 (nextSet r sel h ℓ) ≥
              mnlObjective (fun j => vUCB r sel h j ℓ) r 1 Sstar ∧
            mnlObjective (fun j => vUCB r sel h j ℓ) r 1 Sstar ≥ mnlObjective v r 1 Sstar)) →
      ∃ j, (ℓ ≤ epochsDone r sel h ∧ vUCB r sel h j ℓ < v j) := by
    intro h ⟨hl, hnot⟩
    by_contra hall
    push_neg at hall
    apply hnot
    constructor
    · exact (hsel (fun S => mnlObjective (fun i => vUCBL (pastUpTo r sel h ℓ) i) r 1 S)).2
        Sstar hSstar
    · exact lemma_A_3 𝒮 hdc r hr v (fun j => vUCB r sel h j ℓ) hv0 (fun j => hall j hl)
        Sstar hSstar hopt' hpos
  calc _ ≤ probT v (alg1 r sel) T
          (fun h => ∃ j, (ℓ ≤ epochsDone r sel h ∧ vUCB r sel h j ℓ < v j)) :=
        probT_mono v hv0 _ T _ _ hsub
    _ ≤ ∑ j, probT v (alg1 r sel) T
          (fun h => ℓ ≤ epochsDone r sel h ∧ vUCB r sel h j ℓ < v j) :=
        probT_exists v hv0 _ T (fun j h => ℓ ≤ epochsDone r sel h ∧ vUCB r sel h j ℓ < v j)
    _ ≤ ∑ _j : Fin N, (6 : ℝ) / (N * ℓ) := by
        apply Finset.sum_le_sum
        intro j _
        exact (lemma_4_1 v r 𝒮 sel hTU hdc hne hsel hv0 hv1 hr T ℓ hℓ j).1
    _ ≤ 6 / ℓ := sum_const_bound N ℓ 6 (by norm_num)
