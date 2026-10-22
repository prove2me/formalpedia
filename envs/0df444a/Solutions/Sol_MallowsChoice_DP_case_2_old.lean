-- Prove2me | solution 1 for MallowsChoice.DP.case_2_old
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T02:21:00.064422+00:00
-- url     : https://prove2.me/submissions/3cc0c1b2-c162-4237-ab97-edc8d7ed054c

import Mathlib
import Definitions.Def_MallowsChoice_DP_Setting

open Finset MallowsChoice.DP

namespace MallowsAux

lemma insertRank_injective {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)) :
    Function.Injective (insertRank σ s) := by
  intro x y h
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [insertRank, Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact absurd h.symm (Fin.succAbove_ne _ _)
  | cast i =>
    induction y using Fin.lastCases with
    | last =>
      simp only [insertRank, Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact absurd h (Fin.succAbove_ne _ _)
    | cast j =>
      simp only [insertRank, Fin.lastCases_castSucc] at h
      have := σ.injective (Fin.succAbove_right_injective h)
      rw [this]

noncomputable def insPerm {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)) :
    Equiv.Perm (Fin (m + 1)) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (insertRank_injective σ s))

lemma insPerm_last {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)) :
    insPerm σ s (Fin.last m) = s := by
  simp [insPerm, insertRank]

lemma insPerm_castSucc {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)) (j : Fin m) :
    insPerm σ s j.castSucc = s.succAbove (σ j) := by
  simp [insPerm, insertRank]

lemma rim_sum (θ : ℝ) (m : ℕ) (f : Equiv.Perm (Fin (m + 1)) → ℝ) :
    ∑ τ, rimProb θ (m + 1) τ * f τ =
      ∑ σ : Equiv.Perm (Fin m), ∑ s : Fin (m + 1),
        rimProb θ m σ * alpha θ (s.val + 1) (m + 1) * f (insPerm σ s) := by
  simp only [rimProb]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun s _ => ?_
  have key : ∀ τ : Equiv.Perm (Fin (m + 1)),
      (∀ j, τ j = insertRank σ s j) ↔ τ = insPerm σ s :=
    fun τ => ⟨fun h => Equiv.ext h, fun h j => by rw [h]; rfl⟩
  simp_rw [key, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

lemma gamma_eq (θ : ℝ) (r M : ℕ) :
    gamma θ r M = ∑ k ∈ range M, if k < r then alpha θ (k + 1) M else 0 := by
  induction r with
  | zero => simp [gamma]
  | succ r ih =>
    have h1 : gamma θ (r + 1) M = gamma θ r M + alpha θ (r + 1) M := by
      simp only [gamma]
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [h1, ih]
    have h2 : ∀ k, (if k < r + 1 then alpha θ (k + 1) M else 0) =
        (if k < r then alpha θ (k + 1) M else 0) +
          (if k = r then alpha θ (k + 1) M else 0) := by
      intro k
      by_cases hk : k < r
      · rw [if_pos hk, if_pos (by omega), if_neg (by omega)]; ring
      · by_cases hk2 : k = r
        · subst hk2; simp
        · rw [if_neg (by omega), if_neg hk, if_neg hk2]; ring
    simp_rw [h2]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    congr 1
    split_ifs with hr
    · rfl
    · simp only [mem_range] at hr
      simp only [alpha]
      rw [if_neg (by omega)]

lemma alpha_sum (θ : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ range M, alpha θ (k + 1) M = 1 := by
  have hZ : 0 < ∑ k ∈ range M, Real.exp (-θ * (k : ℝ)) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) (by simp; omega)
  have h1 : ∀ k ∈ range M, alpha θ (k + 1) M =
      Real.exp (-θ * (((M - 1 - k : ℕ)) : ℝ)) / ∑ k ∈ range M, Real.exp (-θ * (k : ℝ)) := by
    intro k hk
    simp only [mem_range] at hk
    simp only [alpha]
    rw [if_pos (by omega)]
    congr 3
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_div,
    Finset.sum_range_reflect (fun k => Real.exp (-θ * (k : ℝ))) M]
  exact div_self hZ.ne'

lemma one_sub_gamma (θ : ℝ) (M : ℕ) (hM : 1 ≤ M) (r : ℕ) :
    1 - gamma θ r M = ∑ k ∈ range M, if k < r then 0 else alpha θ (k + 1) M := by
  rw [← alpha_sum θ M hM, gamma_eq, ← Finset.sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma piProb_fin {n m : ℕ} (θ : ℝ) (S : Finset (Fin n)) (hm : m ≤ n) (a : Fin m) (r : ℕ) :
    piProb θ S (a.val + 1) r m = ∑ σ : Equiv.Perm (Fin m), rimProb θ m σ *
      (if Fin.castLE hm a ∈ S ∧ (σ a).val + 1 = r ∧
          ∀ b : Fin m, Fin.castLE hm b ∈ S → b ≠ a → σ a < σ b then (1 : ℝ) else 0) := by
  unfold piProb
  rw [dif_pos hm, dif_pos ⟨by omega, a.isLt⟩]
  have ha : (⟨a.val + 1 - 1, by omega⟩ : Fin m) = a := Fin.ext (by simp)
  split_ifs with hr
  · simp only [ha]
  · symm
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg]
    · simp
    · rintro ⟨-, h, -⟩
      have := (σ a).isLt
      omega

end MallowsAux

open MallowsAux

namespace MallowsAux

lemma castLE_castSucc' {m n : ℕ} (h : m + 1 ≤ n) (b : Fin m) :
    Fin.castLE h b.castSucc = Fin.castLE (by omega) b := Fin.ext rfl

lemma old_sum {n m : ℕ} (θ : ℝ) (S : Finset (Fin n)) (hmn : m < n) (a : Fin m) (r : ℕ)
    (g : Fin (m + 1) → Prop) [DecidablePred g]
    (hiff : ∀ σ : Equiv.Perm (Fin m), ∀ s : Fin (m + 1),
      (Fin.castLE (Nat.succ_le_of_lt hmn) a.castSucc ∈ S ∧
          (insPerm σ s a.castSucc).val + 1 = r ∧
          ∀ b : Fin (m + 1), Fin.castLE (Nat.succ_le_of_lt hmn) b ∈ S → b ≠ a.castSucc →
            insPerm σ s a.castSucc < insPerm σ s b) ↔
      (Fin.castLE hmn.le a ∈ S ∧ (σ a).val + 1 = r ∧
          ∀ b : Fin m, Fin.castLE hmn.le b ∈ S → b ≠ a → σ a < σ b) ∧ g s) :
    piProb θ S (a.val + 1) r (m + 1) =
      ∑ σ : Equiv.Perm (Fin m), rimProb θ m σ *
        (if Fin.castLE hmn.le a ∈ S ∧ (σ a).val + 1 = r ∧
          ∀ b : Fin m, Fin.castLE hmn.le b ∈ S → b ≠ a → σ a < σ b then (1 : ℝ) else 0) *
        ∑ s : Fin (m + 1), if g s then alpha θ (s.val + 1) (m + 1) else 0 := by
  have h := piProb_fin θ S (Nat.succ_le_of_lt hmn) a.castSucc r
  rw [Fin.val_castSucc] at h
  rw [h, rim_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [if_congr (hiff σ s) rfl rfl]
  split_ifs <;> simp_all

end MallowsAux

theorem case_2_old_sol (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (S : Finset (Fin n))
    (m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (hin : (⟨m, hmn⟩ : Fin n) ∈ S) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ s : ℕ, 1 ≤ s → s ≤ m + 1 →
      piProb θ S i s (m + 1) =
        (1 - gamma θ s (m + 1)) * piProb θ S i s m := by
  intro i hi1 him r _ _
  obtain ⟨a, rfl⟩ : ∃ a : Fin m, i = a.val + 1 := ⟨⟨i - 1, by omega⟩, by simp; omega⟩
  rw [old_sum θ S hmn a r (fun s => ¬ s.val < r), piProb_fin θ S hmn.le a r,
    one_sub_gamma θ (m + 1) (by omega) r]
  · have hs : ∑ s : Fin (m + 1), (if ¬ s.val < r then alpha θ (s.val + 1) (m + 1) else 0) =
        ∑ k ∈ range (m + 1), (if k < r then 0 else alpha θ (k + 1) (m + 1)) := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if ¬ k < r then alpha θ (k + 1) (m + 1) else 0)]
      simp only [ite_not]
    rw [hs, ← Finset.sum_mul, mul_comm]
  · intro σ s
    have hlast : Fin.castLE (Nat.succ_le_of_lt hmn) (Fin.last m) ∈ S := by
      have he : Fin.castLE (Nat.succ_le_of_lt hmn) (Fin.last m) = ⟨m, hmn⟩ := Fin.ext rfl
      rw [he]; exact hin
    rw [Fin.forall_fin_succ']
    simp only [castLE_castSucc', insPerm_castSucc, insPerm_last, ne_eq,
      Fin.castSucc_inj, Fin.succAbove_lt_succAbove_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have h5 := h4 hlast (Fin.castSucc_ne_last a).symm
      rw [Fin.succAbove_lt_iff_castSucc_lt] at h5
      rw [Fin.succAbove_of_castSucc_lt _ _ h5] at h2
      simp only [Fin.val_castSucc] at h2
      refine ⟨⟨h1, h2, h3⟩, ?_⟩
      rw [Fin.lt_def] at h5
      simp only [Fin.val_castSucc] at h5
      omega
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      have h5 : (σ a).castSucc < s := by
        rw [Fin.lt_def]; simp only [Fin.val_castSucc]; omega
      refine ⟨h1, ?_, h3, fun _ _ => ?_⟩
      · rw [Fin.succAbove_of_castSucc_lt _ _ h5]; simpa using h2
      · rw [Fin.succAbove_lt_iff_castSucc_lt]; exact h5

theorem case_1_sol (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (S : Finset (Fin n))
    (m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (hout : (⟨m, hmn⟩ : Fin n) ∉ S) :
    (∀ s : ℕ, piProb θ S (m + 1) s (m + 1) = 0) ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ s : ℕ, 1 ≤ s → s ≤ m + 1 →
        piProb θ S i s (m + 1) =
          (1 - gamma θ s (m + 1)) * piProb θ S i s m +
            gamma θ (s - 1) (m + 1) * piProb θ S i (s - 1) m := by
  have hlast : Fin.castLE (Nat.succ_le_of_lt hmn) (Fin.last m) ∉ S := by
    have he : Fin.castLE (Nat.succ_le_of_lt hmn) (Fin.last m) = ⟨m, hmn⟩ := Fin.ext rfl
    rw [he]; exact hout
  refine ⟨fun r => ?_, ?_⟩
  · have h := piProb_fin θ S (Nat.succ_le_of_lt hmn) (Fin.last m) r
    rw [Fin.val_last] at h
    rw [h]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg (fun hc => hlast hc.1), mul_zero]
  intro i hi1 him r _ _
  obtain ⟨a, rfl⟩ : ∃ a : Fin m, i = a.val + 1 := ⟨⟨i - 1, by omega⟩, by simp; omega⟩
  have h := piProb_fin θ S (Nat.succ_le_of_lt hmn) a.castSucc r
  rw [Fin.val_castSucc] at h
  rw [h, rim_sum, piProb_fin θ S hmn.le a r, piProb_fin θ S hmn.le a (r - 1),
    one_sub_gamma θ (m + 1) (by omega) r, gamma_eq,
    ← Fin.sum_univ_eq_sum_range (fun k => if k < r then 0 else alpha θ (k + 1) (m + 1)),
    ← Fin.sum_univ_eq_sum_range (fun k => if k < r - 1 then alpha θ (k + 1) (m + 1) else 0),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  have hiff : (Fin.castLE (Nat.succ_le_of_lt hmn) a.castSucc ∈ S ∧
          (insPerm σ s a.castSucc).val + 1 = r ∧
          ∀ b : Fin (m + 1), Fin.castLE (Nat.succ_le_of_lt hmn) b ∈ S → b ≠ a.castSucc →
            insPerm σ s a.castSucc < insPerm σ s b) ↔
      (Fin.castLE hmn.le a ∈ S ∧ (s.succAbove (σ a)).val + 1 = r ∧
          ∀ b : Fin m, Fin.castLE hmn.le b ∈ S → b ≠ a → σ a < σ b) := by
    rw [Fin.forall_fin_succ']
    simp only [castLE_castSucc', insPerm_castSucc, insPerm_last, ne_eq,
      Fin.castSucc_inj, Fin.succAbove_lt_succAbove_iff]
    constructor
    · rintro ⟨h1, h2, h3, -⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3, fun hl => absurd hl hlast⟩
  rw [if_congr hiff rfl rfl]
  have hval : (s.succAbove (σ a)).val =
      if (σ a).val < s.val then (σ a).val else (σ a).val + 1 := by
    split_ifs with hlt
    · rw [Fin.succAbove_of_castSucc_lt]
      · simp
      · rw [Fin.lt_def]; simpa using hlt
    · rw [Fin.succAbove_of_le_castSucc]
      · simp
      · rw [Fin.le_def]; simp; omega
  rw [hval]
  by_cases hA : Fin.castLE hmn.le a ∈ S
  · by_cases hB : ∀ b : Fin m, Fin.castLE hmn.le b ∈ S → b ≠ a → σ a < σ b
    · simp only [eq_true hA, eq_true hB, true_and, and_true]
      have hs := s.isLt
      have ha := (σ a).isLt
      split_ifs <;> first | omega | ring
    · simp only [eq_false hB, and_false, if_false, mul_zero, add_zero]
  · simp only [eq_false hA, false_and, if_false, mul_zero, add_zero]

namespace MallowsAux

lemma sum_Icc_one_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Icc 1 m, f i = ∑ a : Fin m, f (a.val + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => f (k + 1))]
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

end MallowsAux

theorem case_2_new_sol (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ)
    (S : Finset (Fin n)) (h1 : (⟨0, hn⟩ : Fin n) ∈ S)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (hin : (⟨m, hmn⟩ : Fin n) ∈ S) :
    ∀ s : ℕ, 1 ≤ s → s ≤ m + 1 →
      piProb θ S (m + 1) s (m + 1) =
        alpha θ s (m + 1) *
          ∑ i ∈ Icc 1 m, ∑ ℓ ∈ Icc s n, piProb θ S i ℓ m := by
  intro r hr1 hr2
  have hlast : Fin.castLE (Nat.succ_le_of_lt hmn) (Fin.last m) ∈ S := by
    have he : Fin.castLE (Nat.succ_le_of_lt hmn) (Fin.last m) = ⟨m, hmn⟩ := Fin.ext rfl
    rw [he]; exact hin
  have h := piProb_fin θ S (Nat.succ_le_of_lt hmn) (Fin.last m) r
  rw [Fin.val_last] at h
  rw [h, rim_sum, sum_Icc_one_eq, Finset.mul_sum]
  -- RHS inner sums
  have hinner : ∀ a : Fin m, ∑ ℓ ∈ Icc r n, piProb θ S (a.val + 1) ℓ m =
      ∑ σ : Equiv.Perm (Fin m), rimProb θ m σ *
        (if Fin.castLE hmn.le a ∈ S ∧
          (∀ b : Fin m, Fin.castLE hmn.le b ∈ S → b ≠ a → σ a < σ b) ∧ r ≤ (σ a).val + 1
          then (1 : ℝ) else 0) := by
    intro a
    simp_rw [piProb_fin θ S hmn.le a]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun σ _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    have : ∀ ℓ, (if Fin.castLE hmn.le a ∈ S ∧ (σ a).val + 1 = ℓ ∧
          ∀ b : Fin m, Fin.castLE hmn.le b ∈ S → b ≠ a → σ a < σ b then (1 : ℝ) else 0) =
        if (σ a).val + 1 = ℓ then (if Fin.castLE hmn.le a ∈ S ∧
          (∀ b : Fin m, Fin.castLE hmn.le b ∈ S → b ≠ a → σ a < σ b) then (1 : ℝ) else 0)
          else 0 := by
      intro ℓ
      by_cases hl : (σ a).val + 1 = ℓ
      · simp only [hl, true_and, if_true]
      · simp only [hl, false_and, and_false, if_false]
    simp_rw [this]
    rw [Finset.sum_ite_eq]
    have ha := (σ a).isLt
    by_cases hra : r ≤ (σ a).val + 1
    · rw [if_pos (by simp; omega)]
      simp only [hra, and_true]
    · rw [if_neg (by simp; omega)]
      simp only [hra, and_false, if_false]
  simp_rw [hinner, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  -- LHS: only s = r - 1 contributes
  have hL : ∀ s : Fin (m + 1),
      rimProb θ m σ * alpha θ (s.val + 1) (m + 1) *
        (if Fin.castLE (Nat.succ_le_of_lt hmn) (Fin.last m) ∈ S ∧
            (insPerm σ s (Fin.last m)).val + 1 = r ∧
            ∀ b : Fin (m + 1), Fin.castLE (Nat.succ_le_of_lt hmn) b ∈ S → b ≠ Fin.last m →
              insPerm σ s (Fin.last m) < insPerm σ s b then (1 : ℝ) else 0) =
      if s.val + 1 = r then rimProb θ m σ * alpha θ r (m + 1) *
        (if ∀ j : Fin m, Fin.castLE hmn.le j ∈ S → r - 1 ≤ (σ j).val then (1 : ℝ) else 0)
      else 0 := by
    intro s
    simp only [Fin.forall_fin_succ']
    simp only [castLE_castSucc', insPerm_castSucc, insPerm_last, ne_eq,
      Fin.castSucc_ne_last, not_false_eq_true, not_true_eq_false, forall_const,
      IsEmpty.forall_iff, and_true, eq_true hlast, true_and, Fin.lt_succAbove_iff_le_castSucc]
    by_cases hs : s.val + 1 = r
    · subst hs
      rw [if_pos rfl]
      have : ∀ j : Fin m, (s ≤ (σ j).castSucc ↔ s.val + 1 - 1 ≤ (σ j).val) := by
        intro j; rw [Fin.le_def]; simp
      simp only [this, true_and]
    · rw [if_neg hs]
      simp [hs]
  simp_rw [hL]
  rw [Finset.sum_eq_single (⟨r - 1, by omega⟩ : Fin (m + 1))]
  · rw [if_pos (by simp; omega)]
    simp_rw [← Finset.mul_sum]
    rw [mul_comm (rimProb θ m σ) (alpha θ r (m + 1)), mul_assoc]
    congr 2
    -- the unique earliest offered product
    obtain ⟨jst, hjS, hjmin⟩ := Finset.exists_min_image
      (univ.filter fun j : Fin m => Fin.castLE hmn.le j ∈ S) (fun j => σ j)
      ⟨⟨0, hm⟩, by
        simp only [mem_filter, mem_univ, true_and]
        exact (show Fin.castLE hmn.le ⟨0, hm⟩ = ⟨0, hn⟩ from Fin.ext rfl) ▸ h1⟩
    simp only [mem_filter, mem_univ, true_and] at hjS hjmin
    have hjst : ∀ b : Fin m, Fin.castLE hmn.le b ∈ S → b ≠ jst → σ jst < σ b := by
      intro b hb hne
      exact lt_of_le_of_ne (hjmin b hb) (fun h => hne (σ.injective h).symm)
    rw [Finset.sum_eq_single jst]
    · simp only [eq_true hjS, eq_true hjst, true_and]
      by_cases hc : r ≤ (σ jst).val + 1
      · rw [if_pos hc, if_pos]
        intro j hj
        have := hjmin j hj
        rw [Fin.le_def] at this
        omega
      · rw [if_neg hc, if_neg]
        intro hall
        have := hall jst hjS
        omega
    · intro b _ hb
      rw [if_neg]
      rintro ⟨hbS, hbmin, -⟩
      have h1' := hbmin jst hjS (Ne.symm hb)
      have h2' := hjmin b hbS
      exact absurd h2' (not_le.mpr h1')
    · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp
    omega
  · simp

theorem solution (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (S : Finset (Fin n))
    (m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (hin : (⟨m, hmn⟩ : Fin n) ∈ S) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ s : ℕ, 1 ≤ s → s ≤ m + 1 →
      piProb θ S i s (m + 1) =
        (1 - gamma θ s (m + 1)) * piProb θ S i s m :=
  case_2_old_sol n θ hθ S m hm hmn hin
