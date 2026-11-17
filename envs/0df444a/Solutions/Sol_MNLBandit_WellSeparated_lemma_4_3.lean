-- Prove2me | solution 1 for MNLBandit.WellSeparated.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-16T12:54:43.79262+00:00
-- url     : https://prove2.me/submissions/62c9fe9e-6e01-486a-a1fd-385c822899ca

import Definitions.Def_MNLBandit_WellSeparated_Setting
import Theorems.Thm_MNLBandit_WellSeparated_lemma_4_1
import Theorems.Thm_MNLBandit_UCB_lemma_A_4
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open MNLBandit.WellSeparated ChoiceCDLP.MNL

private theorem histProb_nonneg {N T : ℕ} (v : Fin N → ℝ)
    (hv : ∀ i, 0 ≤ v i) (π : MNLBandit.UCB.Policy N)
    (h : Fin T → Option (Fin N)) : 0 ≤ histProb v π T h := by
  apply Finset.prod_nonneg
  intro t _
  let S := π t (histPrefix h t)
  change 0 ≤ MNLBandit.UCB.choiceProb v S (h t)
  have hd : 0 ≤ 1 + ∑ j ∈ S, v j :=
    add_nonneg zero_le_one (Finset.sum_nonneg (fun j _ => hv j))
  cases h t with
  | none => exact div_nonneg zero_le_one hd
  | some j =>
    simp only [MNLBandit.UCB.choiceProb]
    split
    · exact div_nonneg (hv j) hd
    · exact le_rfl

/-- A finite union bound with the history law used in the well-separated mission. -/
private theorem probT_union₂_le {N T : ℕ} {J : Type*} [Fintype J]
    (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : MNLBandit.UCB.Policy N)
    (E : (Fin T → Option (Fin N)) → Prop)
    (P Q : J → (Fin T → Option (Fin N)) → Prop)
    (cover : ∀ h, E h → ∃ i, P i h ∨ Q i h) :
    probT v π T E ≤ ∑ i, (probT v π T (P i) + probT v π T (Q i)) := by
  classical
  simp only [probT, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro h _
  let w := histProb v π T h
  have hw : 0 ≤ w := histProb_nonneg v hv π h
  have nonneg (i : J) : 0 ≤ (if P i h then w else 0) + (if Q i h then w else 0) := by
    exact add_nonneg (by split <;> simp [hw]) (by split <;> simp [hw])
  change (if E h then w else 0) ≤ ∑ i, ((if P i h then w else 0) + (if Q i h then w else 0))
  split_ifs with he
  · obtain ⟨i, hi⟩ := cover h he
    have hterm : w ≤ (if P i h then w else 0) + (if Q i h then w else 0) := by
      rcases hi with hp | hq
      · simp only [if_pos hp]
        apply le_add_of_nonneg_right
        split
        · exact hw
        · exact le_rfl
      · simp only [if_pos hq]
        apply le_add_of_nonneg_left
        split
        · exact hw
        · exact le_rfl
    exact hterm.trans (Finset.single_le_sum (fun j _ => nonneg j) (Finset.mem_univ i))
  · exact Finset.sum_nonneg (fun j _ => nonneg j)

theorem solution (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    probT v (alg1 r sel) T
        (fun h => ℓ ≤ epochsDone r sel h ∧
          (∀ i ∈ epochSet r sel h (ℓ + 1), 1 ≤ Tcount r sel h i ℓ) ∧
          ∑ i ∈ epochSet r sel h (ℓ + 1),
              (C₁ * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
                + C₂ * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            < (1 + ∑ j ∈ epochSet r sel h (ℓ + 1), v j) *
                (mnlObjective (fun j => vUCB r sel h j ℓ) r 1 (epochSet r sel h (ℓ + 1))
                  - revenue v r (epochSet r sel h (ℓ + 1))))
      ≤ 13 / (ℓ : ℝ) := by 
  classical
  let π := alg1 r sel
  let H := Fin T → Option (Fin N)
  let S := fun h : H => epochSet r sel h (ℓ+1)
  let u := fun (h : H) j => vUCB r sel h j ℓ
  let A := fun (h : H) i =>
    C₁ * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ) +
      C₂ * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ
  let P := fun (i : Fin N) (h : H) => ℓ ≤ epochsDone r sel h ∧ u h i < v i
  let Q := fun (i : Fin N) (h : H) =>
    ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧ A h i < u h i - v i
  let E := fun h : H =>
    ℓ ≤ epochsDone r sel h ∧ (∀ i ∈ S h, 1 ≤ Tcount r sel h i ℓ) ∧
      (∑ i ∈ S h, A h i) < (1 + ∑ j ∈ S h, v j) *
        (mnlObjective (u h) r 1 (S h) - revenue v r (S h))
  change probT v π T E ≤ _
  have hlo : ∀ i, 0 ≤ v i := fun i => (hv i).1
  have cover (h : H) (he : E h) : ∃ i, P i h ∨ Q i h := by
    by_contra hn
    have hn' (i : Fin N) : ¬ (P i h ∨ Q i h) := fun hi => hn ⟨i, hi⟩
    have hu (i : Fin N) : v i ≤ u h i :=
      le_of_not_gt (fun hi => hn' i (Or.inl ⟨he.1, hi⟩))
    have hA (i : Fin N) (hi : i ∈ S h) : u h i - v i ≤ A h i :=
      le_of_not_gt (fun hj => hn' i (Or.inr ⟨he.1, he.2.1 i hi, hj⟩))
    have hd : 0 < 1 + ∑ j ∈ S h, v j :=
      add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ => hlo j))
    have hg := MNLBandit.UCB.lemma_A_4 r hr v (u h) (S h) (fun j _ => hlo j) (fun j _ => hu j)
    have hg' : (1 + ∑ j ∈ S h, v j) *
        (mnlObjective (u h) r 1 (S h) - revenue v r (S h)) ≤ ∑ j ∈ S h, (u h j - v j) := by
      simpa only [revenue, mul_comm] using (le_div_iff₀ hd).mp hg
    exact (not_lt_of_ge (hg'.trans (Finset.sum_le_sum hA))) he.2.2
  have hbound (i : Fin N) :=
    MNLBandit.WellSeparated.lemma_4_1 N v r 𝒮 sel hTU hdown hv hr hsel T ℓ hℓ i
  calc
    probT v π T E ≤ ∑ i, (probT v π T (P i) + probT v π T (Q i)) :=
      probT_union₂_le v hlo π E P Q cover
    _ ≤ ∑ _i : Fin N, (6 / ((N : ℝ) * ℓ) + 7 / ((N : ℝ) * ℓ)) :=
      Finset.sum_le_sum (fun i _ => add_le_add (hbound i).1 (hbound i).2)
    _ ≤ 13 / (ℓ : ℝ) := by
      by_cases hN : N = 0
      · subst N
        simp
        positivity
      · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
        have hℓr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp <;> norm_num
