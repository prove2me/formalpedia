-- Prove2me | solution 1 for LinExchangeSP.ZPlus.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:18:50.698808+00:00
-- url     : https://prove2.me/submissions/fea02eef-5cb9-4197-9a5a-3071411f1868

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace Aux_LinExchangeSP_ZPlus_lemma_7_2

open LinExchangeSP.ZPlus

/-- Invariant after `n` elimination steps. -/
def Inv {l t : ℕ} (T : Matrix (Fin l) (Fin t) ℚ) (n : ℕ)
    (Y : Matrix (Fin l) (Fin l) ℚ) (U : Matrix (Fin l) (Fin t) ℚ) : Prop :=
  U = Y * T ∧
  (∀ a b, 0 ≤ Y a b) ∧
  (∀ (i : Fin l) (j : Fin t), (i : ℕ) ≠ (j : ℕ) → U i j ≤ 0) ∧
  (∀ j : Fin t, n ≤ (j : ℕ) → 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin l => n ≤ (i : ℕ)), U i j) ∧
  (∀ (i : Fin l) (j : Fin t), (j : ℕ) < n → (j : ℕ) < (i : ℕ) → U i j = 0) ∧
  (∀ (i : Fin l) (j : Fin t), (i : ℕ) < n → (i : ℕ) = (j : ℕ) → U i j = 0 ∨ U i j = 1) ∧
  (∀ (i : Fin l) (j : Fin t), n ≤ (i : ℕ) → n ≤ (j : ℕ) → U i j ≤ T i j) ∧
  (∀ (k : Fin t) (i : Fin l), (k : ℕ) < n → (k : ℕ) < (i : ℕ) → T i k < 0 →
    ∀ hk : (k : ℕ) < l, U ⟨k, hk⟩ k = 1)

theorem inv_zero {l t : ℕ} (T : Matrix (Fin l) (Fin t) ℚ) (hT : IsZPlus T) : Inv T 0 1 T := by
  unfold Inv
  refine ⟨(Matrix.one_mul T).symm, ?_, hT.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [Matrix.one_apply]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  · intro j _
    rw [Finset.filter_true_of_mem (fun i _ => Nat.zero_le _)]
    exact hT.2 j
  · intro i j hj
    omega
  · intro i j hi
    omega
  · intro i j _ _
    exact le_rfl
  · intro k i hk
    omega

theorem sum_split {l : ℕ} (n : ℕ) (hn : n < l) (f : Fin l → ℚ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin l => n ≤ (i : ℕ)), f i =
      f ⟨n, hn⟩ + ∑ i ∈ Finset.univ.filter (fun i : Fin l => n + 1 ≤ (i : ℕ)), f i := by
  have hset : Finset.univ.filter (fun i : Fin l => n ≤ (i : ℕ)) =
      insert ⟨n, hn⟩ (Finset.univ.filter (fun i : Fin l => n + 1 ≤ (i : ℕ))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨n, hn⟩ : Fin l) ∉ Finset.univ.filter (fun i : Fin l => n + 1 ≤ (i : ℕ)) := by
    simp
  rw [hset, Finset.sum_insert hnot]

theorem step_inv {l t : ℕ} (T : Matrix (Fin l) (Fin t) ℚ) (n : ℕ) (hn : n < l) (hnt : n < t)
    (p : Matrix (Fin l) (Fin l) ℚ × Matrix (Fin l) (Fin t) ℚ) (hinv : Inv T n p.1 p.2) :
    Inv T (n + 1) (elimStep n p).1 (elimStep n p).2 := by
  obtain ⟨Y, U⟩ := p
  obtain ⟨I1, I2, I3, I4, I5, I6, I7, I8⟩ := hinv
  simp only at I1 I2 I3 I4 I5 I6 I7 I8
  have hstep : elimStep n (Y, U) =
      if U ⟨n, hn⟩ ⟨n, hnt⟩ = 0 then (Y, U) else
        (rowOps ⟨n, hn⟩ (U ⟨n, hn⟩ ⟨n, hnt⟩) (fun i => U i ⟨n, hnt⟩) Y,
         rowOps ⟨n, hn⟩ (U ⟨n, hn⟩ ⟨n, hnt⟩) (fun i => U i ⟨n, hnt⟩) U) := by
    unfold elimStep
    rw [dif_pos ⟨hn, hnt⟩]
  rw [hstep]
  -- column n below the pivot
  have hcoln := I4 ⟨n, hnt⟩ (le_refl n)
  rw [sum_split n hn] at hcoln
  have hbelow : ∀ i : Fin l, n + 1 ≤ (i : ℕ) → U i ⟨n, hnt⟩ ≤ 0 := by
    intro i hi
    exact I3 i ⟨n, hnt⟩ (by simp only [ne_eq]; omega)
  have hrow : ∀ j : Fin t, n + 1 ≤ (j : ℕ) → U ⟨n, hn⟩ j ≤ 0 := by
    intro j hj
    exact I3 ⟨n, hn⟩ j (by simp only [ne_eq]; omega)
  by_cases hp : U ⟨n, hn⟩ ⟨n, hnt⟩ = 0
  · rw [if_pos hp]
    unfold Inv
    simp only
    -- the whole column below the (zero) pivot vanishes
    have hcolzero : ∀ i : Fin l, n < (i : ℕ) → U i ⟨n, hnt⟩ = 0 := by
      rw [hp, zero_add] at hcoln
      have hall : ∀ i ∈ Finset.univ.filter (fun i : Fin l => n + 1 ≤ (i : ℕ)),
          U i ⟨n, hnt⟩ ≤ 0 := by
        intro i hi
        rw [Finset.mem_filter] at hi
        exact hbelow i hi.2
      have hz := (Finset.sum_eq_zero_iff_of_nonpos hall).mp
        (le_antisymm (Finset.sum_nonpos hall) hcoln)
      intro i hi
      exact hz i (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩)
    refine ⟨I1, I2, I3, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have h1 := I4 j (by omega)
      rw [sum_split n hn] at h1
      have h2 := hrow j hj
      linarith
    · intro i j hj hji
      by_cases hjn : (j : ℕ) < n
      · exact I5 i j hjn hji
      · have hjeq : j = ⟨n, hnt⟩ := Fin.ext (by simp only; omega)
        rw [hjeq]
        exact hcolzero i (by omega)
    · intro i j hi hij
      by_cases hin : (i : ℕ) < n
      · exact I6 i j hin hij
      · have hieq : i = ⟨n, hn⟩ := Fin.ext (by simp only; omega)
        have hjeq : j = ⟨n, hnt⟩ := Fin.ext (by simp only; omega)
        rw [hieq, hjeq]
        exact Or.inl hp
    · intro i j hi hj
      exact I7 i j (by omega) (by omega)
    · intro k i hk hki hTik hkl
      by_cases hkn : (k : ℕ) < n
      · exact I8 k i hkn hki hTik hkl
      · exfalso
        have hkeq : k = ⟨n, hnt⟩ := Fin.ext (by simp only; omega)
        rw [hkeq] at hTik
        have h1 := I7 i ⟨n, hnt⟩ (by omega) (le_refl n)
        have h2 := hcolzero i (by omega)
        linarith
  · rw [if_neg hp]
    unfold Inv
    simp only
    -- the pivot is positive
    have hsum_below : ∑ i ∈ Finset.univ.filter (fun i : Fin l => n + 1 ≤ (i : ℕ)),
        U i ⟨n, hnt⟩ ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      rw [Finset.mem_filter] at hi
      exact hbelow i hi.2
    have hpos : 0 < U ⟨n, hn⟩ ⟨n, hnt⟩ := lt_of_le_of_ne (by linarith) (Ne.symm hp)
    obtain ⟨piv, hpiv⟩ : ∃ piv, piv = U ⟨n, hn⟩ ⟨n, hnt⟩ := ⟨_, rfl⟩
    rw [← hpiv]
    rw [← hpiv] at hpos hcoln
    have hro : ∀ {β : Type} (A : Matrix (Fin l) β ℚ) (i : Fin l) (j : β),
        rowOps ⟨n, hn⟩ piv (fun i => U i ⟨n, hnt⟩) A i j =
          if i = ⟨n, hn⟩ then A ⟨n, hn⟩ j / piv
          else if (⟨n, hn⟩ : Fin l) < i then A i j - U i ⟨n, hnt⟩ / piv * A ⟨n, hn⟩ j
          else A i j := by
      intro β A i j
      rfl
    have hlt : ∀ i : Fin l, (⟨n, hn⟩ : Fin l) < i ↔ n < (i : ℕ) := by
      intro i
      rw [Fin.lt_iff_val_lt_val]
    have heq : ∀ i : Fin l, i = ⟨n, hn⟩ ↔ (i : ℕ) = n := by
      intro i
      rw [Fin.ext_iff]
    have hUe : ∀ a b, U a b = ∑ m, Y a m * T m b := fun a b => by
      rw [I1, Matrix.mul_apply]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- I1
      ext i j
      rw [hro, Matrix.mul_apply]
      by_cases h1 : i = ⟨n, hn⟩
      · rw [if_pos h1, hUe, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro m _
        rw [hro, if_pos h1]
        ring
      · rw [if_neg h1]
        by_cases h2 : (⟨n, hn⟩ : Fin l) < i
        · rw [if_pos h2, hUe i j, hUe ⟨n, hn⟩ j, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro m _
          rw [hro, if_neg h1, if_pos h2]
          ring
        · rw [if_neg h2, hUe i j]
          apply Finset.sum_congr rfl
          intro m _
          rw [hro, if_neg h1, if_neg h2]
    · -- I2
      intro a b
      rw [hro]
      split_ifs with h1 h2
      · exact div_nonneg (I2 _ _) hpos.le
      · have ha : U a ⟨n, hnt⟩ ≤ 0 := hbelow a (by rw [hlt] at h2; omega)
        have h3 : U a ⟨n, hnt⟩ / piv * Y ⟨n, hn⟩ b ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg ha hpos.le) (I2 _ _)
        have h4 := I2 a b
        linarith
      · exact I2 a b
    · -- I3
      intro i j hij
      rw [hro]
      split_ifs with h1 h2
      · have hi : (i : ℕ) = n := (heq i).mp h1
        exact div_nonpos_of_nonpos_of_nonneg (I3 _ j (by simp only; omega)) hpos.le
      · have hi : n < (i : ℕ) := (hlt i).mp h2
        by_cases hjn : (j : ℕ) = n
        · have hjeq : j = ⟨n, hnt⟩ := Fin.ext (by simp only; omega)
          rw [hjeq, ← hpiv]
          have : U i ⟨n, hnt⟩ / piv * piv = U i ⟨n, hnt⟩ := div_mul_cancel₀ _ (ne_of_gt hpos)
          linarith
        · have ha : U i ⟨n, hnt⟩ ≤ 0 := hbelow i (by omega)
          have hb : U ⟨n, hn⟩ j ≤ 0 := I3 _ j (by simp only; omega)
          have hc : U i j ≤ 0 := I3 i j hij
          have h3 : 0 ≤ U i ⟨n, hnt⟩ / piv * U ⟨n, hn⟩ j :=
            mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg ha hpos.le) hb
          linarith
      · exact I3 i j hij
    · -- I4
      intro j hj
      have hrw : ∀ i ∈ Finset.univ.filter (fun i : Fin l => n + 1 ≤ (i : ℕ)),
          rowOps ⟨n, hn⟩ piv (fun i => U i ⟨n, hnt⟩) U i j =
            U i j - U i ⟨n, hnt⟩ / piv * U ⟨n, hn⟩ j := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [hro, if_neg (show ¬ (i = ⟨n, hn⟩) from fun h => by rw [heq] at h; omega),
          if_pos ((hlt i).mpr (by omega))]
      rw [Finset.sum_congr rfl hrw, Finset.sum_sub_distrib]
      have hfac : ∑ i ∈ Finset.univ.filter (fun i : Fin l => n + 1 ≤ (i : ℕ)),
          U i ⟨n, hnt⟩ / piv * U ⟨n, hn⟩ j =
            U ⟨n, hn⟩ j / piv * ∑ i ∈ Finset.univ.filter (fun i : Fin l => n + 1 ≤ (i : ℕ)),
              U i ⟨n, hnt⟩ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hfac]
      have hj4 := I4 j (by omega)
      rw [sum_split n hn] at hj4
      have hb : U ⟨n, hn⟩ j ≤ 0 := hrow j hj
      have ha : U ⟨n, hn⟩ j / piv ≤ 0 := div_nonpos_of_nonpos_of_nonneg hb hpos.le
      have key : 0 ≤ -(U ⟨n, hn⟩ j / piv) *
          (piv + ∑ i ∈ Finset.univ.filter (fun i : Fin l => n + 1 ≤ (i : ℕ)), U i ⟨n, hnt⟩) :=
        mul_nonneg (by linarith) hcoln
      have hapiv : U ⟨n, hn⟩ j / piv * piv = U ⟨n, hn⟩ j := div_mul_cancel₀ _ (ne_of_gt hpos)
      nlinarith
    · -- I5
      intro i j hj hji
      rw [hro]
      split_ifs with h1 h2
      · have hi : (i : ℕ) = n := (heq i).mp h1
        rw [I5 ⟨n, hn⟩ j (by omega) (by simp only; omega), zero_div]
      · have hi : n < (i : ℕ) := (hlt i).mp h2
        by_cases hjn : (j : ℕ) < n
        · rw [I5 i j hjn (by omega), I5 ⟨n, hn⟩ j hjn (by simp only; omega), mul_zero, sub_zero]
        · have hjeq : j = ⟨n, hnt⟩ := Fin.ext (by simp only; omega)
          rw [hjeq, ← hpiv, div_mul_cancel₀ _ (ne_of_gt hpos), sub_self]
      · have hi : (i : ℕ) < n := by
          have h1' : (i : ℕ) ≠ n := fun h => h1 ((heq i).mpr h)
          have h2' : ¬ n < (i : ℕ) := fun h => h2 ((hlt i).mpr h)
          omega
        exact I5 i j (by omega) hji
    · -- I6
      intro i j hi hij
      rw [hro]
      split_ifs with h1 h2
      · right
        have hjeq : j = ⟨n, hnt⟩ := Fin.ext (by rw [← hij]; exact (heq i).mp h1)
        rw [hjeq, ← hpiv]
        exact div_self (ne_of_gt hpos)
      · exfalso
        have := (hlt i).mp h2
        omega
      · have h1' : (i : ℕ) ≠ n := fun h => h1 ((heq i).mpr h)
        exact I6 i j (by omega) hij
    · -- I7
      intro i j hi hj
      rw [hro, if_neg (show ¬ (i = ⟨n, hn⟩) from fun h => by rw [heq] at h; omega),
        if_pos ((hlt i).mpr (by omega))]
      have ha : U i ⟨n, hnt⟩ ≤ 0 := hbelow i (by omega)
      have hb : U ⟨n, hn⟩ j ≤ 0 := hrow j (by omega)
      have h3 : 0 ≤ U i ⟨n, hnt⟩ / piv * U ⟨n, hn⟩ j :=
        mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg ha hpos.le) hb
      have h4 := I7 i j (by omega) (by omega)
      linarith
    · -- I8
      intro k i hk hki hTik hkl
      rw [hro]
      by_cases hkn : (k : ℕ) < n
      · have h1 : ¬ ((⟨k, hkl⟩ : Fin l) = ⟨n, hn⟩) := fun h => by
          rw [heq] at h; simp only at h; omega
        have h2 : ¬ ((⟨n, hn⟩ : Fin l) < ⟨k, hkl⟩) := fun h => by
          rw [hlt] at h; simp only at h; omega
        rw [if_neg h1, if_neg h2]
        exact I8 k i hkn hki hTik hkl
      · have hkn' : (k : ℕ) = n := by omega
        have h1 : (⟨k, hkl⟩ : Fin l) = ⟨n, hn⟩ := Fin.ext (by simp only; omega)
        have hkeq : k = ⟨n, hnt⟩ := Fin.ext (by simp only; omega)
        rw [if_pos h1, hkeq, ← hpiv]
        exact div_self (ne_of_gt hpos)

theorem inv_all {l t : ℕ} (T : Matrix (Fin l) (Fin t) ℚ) (hT : IsZPlus T) :
    ∀ n, n ≤ min l t → Inv T n (elimAux T n).1 (elimAux T n).2 := by
  intro n
  induction n with
  | zero => intro _; exact inv_zero T hT
  | succ n ih =>
    intro hn
    have hnl : n < l := by omega
    have hnt : n < t := by omega
    exact step_inv T n hnl hnt (elimAux T n) (ih (by omega))

end Aux_LinExchangeSP_ZPlus_lemma_7_2

open LinExchangeSP.ZPlus Aux_LinExchangeSP_ZPlus_lemma_7_2 in
theorem solution {l t : ℕ} (T : Matrix (Fin l) (Fin t) ℚ) (hT : IsZPlus T) :
    (gaussElim T).2 = (gaussElim T).1 * T ∧
    (∀ i j, 0 ≤ (gaussElim T).1 i j) ∧
    (∀ (i : Fin l) (j : Fin t), (j : ℕ) < (i : ℕ) → (gaussElim T).2 i j = 0) ∧
    (∀ (i : Fin l) (j : Fin t), (i : ℕ) = (j : ℕ) →
      (gaussElim T).2 i j = 0 ∨ (gaussElim T).2 i j = 1) ∧
    (∀ (i : Fin l) (j : Fin t), (i : ℕ) ≠ (j : ℕ) → (gaussElim T).2 i j ≤ 0) ∧
    (∀ (k : Fin t) (i : Fin l), (k : ℕ) < (i : ℕ) → T i k < 0 →
      ∀ hk : (k : ℕ) < l, (gaussElim T).2 ⟨k, hk⟩ k = 1) := by
  obtain ⟨I1, I2, I3, _, I5, I6, _, I8⟩ := inv_all T hT (min l t) le_rfl
  unfold gaussElim
  refine ⟨I1, I2, ?_, ?_, I3, ?_⟩
  · intro i j hji
    have hi := i.2
    have hj := j.2
    exact I5 i j (by omega) hji
  · intro i j hij
    have hi := i.2
    have hj := j.2
    exact I6 i j (by omega) hij
  · intro k i hki hTik hk
    have hkt := k.2
    exact I8 k i (by omega) hki hTik hk
