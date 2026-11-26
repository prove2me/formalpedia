-- Prove2me | solution 1 for NisanRonen.Rounding.threshold_implication_controls_rounded_bundle_load
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T08:02:13.671414+00:00
-- url     : https://prove2.me/submissions/07a8bc9b-5f99-4c34-87ba-3439ffd3a153

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

open NisanRonen.Rounding
open scoped BigOperators

set_option autoImplicit false

private theorem choose_bounded_sum {α : Type} [DecidableEq α] (s : Finset α)
    (L U : α → ℤ) (h : ∀ j ∈ s, L j ≤ U j) (m : ℤ)
    (hL : (∑ j ∈ s, L j) ≤ m) (hU : m ≤ ∑ j ∈ s, U j) :
    ∃ D : α → ℤ, (∀ j ∈ s, L j ≤ D j ∧ D j ≤ U j) ∧ (∑ j ∈ s, D j) = m := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty =>
    refine ⟨L, by simp, ?_⟩
    simp at hL hU
    simpa using le_antisymm hL hU
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha] at hL hU
    let q := max (L a) (m - ∑ j ∈ s, U j)
    have hqa : L a ≤ q := le_max_left _ _
    have hqu : q ≤ U a := max_le (h a (Finset.mem_insert_self _ _)) (by omega)
    have hremL : (∑ j ∈ s, L j) ≤ m - q := by
      have hsum := Finset.sum_le_sum (f := L) (g := U)
        (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have hq : q ≤ m - ∑ j ∈ s, L j := max_le (by omega) (by omega)
      omega
    have hremU : m - q ≤ ∑ j ∈ s, U j := by
      have hq : m - ∑ j ∈ s, U j ≤ q := le_max_right _ _
      omega
    obtain ⟨D, hd, hds⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      (m-q) hremL hremU
    let D' := Function.update D a q
    refine ⟨D', ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · simpa [D'] using And.intro hqa hqu
      · have hjne : j ≠ a := fun e => ha (e ▸ hj)
        simpa [D', Function.update_of_ne hjne] using hd j hj
    · have he : (∑ j ∈ s, D' j) = ∑ j ∈ s, D j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjne : j ≠ a := fun e => ha (e ▸ hj)
        simp [D', Function.update_of_ne hjne]
      rw [Finset.sum_insert ha, he, hds]
      simp [D']

private theorem time_ge {δ u : ℝ} (hδ : 0 < δ) : u ≤ roundUp δ u := by
  have hm := mul_le_mul_of_nonneg_left (Int.le_ceil (u / δ)) hδ.le
  rw [mul_comm δ (u / δ), div_mul_cancel₀ _ hδ.ne'] at hm
  exact hm

private theorem time_mono {δ : ℝ} (hδ : 0 < δ) {u v : ℝ} (h : u ≤ v) :
    roundUp δ u ≤ roundUp δ v := by
  unfold roundUp
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast Int.ceil_mono (div_le_div_of_nonneg_right h hδ.le)) hδ.le

private theorem time_grid {δ : ℝ} (hδ : 0 < δ) (z : ℤ) :
    roundUp δ (δ * (z : ℝ)) = δ * (z : ℝ) := by
  simp [roundUp, mul_div_cancel_left₀ _ hδ.ne']

private theorem cap_row {k : ℕ} {a b δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Fin k)) (row : Fin k → ℝ) (hrow : ∀ j, a ≤ row j ∧ row j ≤ b)
    (m : ℤ) (hfloor : (∑ _j ∈ S, roundUp δ a) ≤ δ * (m : ℝ)) :
    ∃ newRow : Fin k → ℝ, (∀ j, a ≤ newRow j ∧ newRow j ≤ b) ∧
      (∀ j ∉ S, newRow j = row j) ∧
      (∀ j, roundUp δ (newRow j) ≤ roundUp δ (row j)) ∧
      (∑ j ∈ S, roundUp δ (newRow j)) = min (∑ j ∈ S, roundUp δ (row j)) (δ * (m : ℝ)) := by
  classical
  let L : ℤ := ⌈a / δ⌉
  let U (j : Fin k) : ℤ := ⌈row j / δ⌉
  let z := min (∑ j ∈ S, U j) m
  have hLU (j : Fin k) : L ≤ U j :=
    Int.ceil_mono (div_le_div_of_nonneg_right (hrow j).1 hδ.le)
  have hLf : (∑ _j ∈ S, L) ≤ m := by
    have hm : δ * (↑(∑ _j ∈ S, L) : ℝ) ≤ δ * (m : ℝ) := by
      simpa only [Int.cast_sum, Finset.mul_sum, L, roundUp] using hfloor
    exact_mod_cast (le_of_mul_le_mul_left hm hδ)
  obtain ⟨D, hd, hsum⟩ := choose_bounded_sum S (fun _ => L) U
    (fun j _ => hLU j) z
    (le_min (Finset.sum_le_sum (fun j _ => hLU j)) hLf) (min_le_left _ _)
  let newRow (j : Fin k) := if j ∈ S then min (row j) (δ * (D j : ℝ)) else row j
  have hround (j : Fin k) (hj : j ∈ S) : roundUp δ (newRow j) = δ * (D j : ℝ) := by
    have hD : δ * (D j : ℝ) ≤ roundUp δ (row j) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (hd j hj).2) hδ.le
    change roundUp δ (if j ∈ S then min (row j) (δ * (D j : ℝ)) else row j) = _
    rw [if_pos hj]
    by_cases hh : row j ≤ δ * (D j : ℝ)
    · rw [min_eq_left hh]
      exact le_antisymm (by simpa [time_grid hδ] using time_mono hδ hh) hD
    · rw [min_eq_right (le_of_not_ge hh), time_grid hδ]
  refine ⟨newRow, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ S
    · have hmin : a ≤ δ * (D j : ℝ) := (time_ge hδ).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast (hd j hj).1) hδ.le)
      exact ⟨by simpa only [newRow, if_pos hj] using le_min (hrow j).1 hmin,
        by simpa only [newRow, if_pos hj] using (min_le_left _ _).trans (hrow j).2⟩
    · simpa [newRow, hj] using hrow j
  · intro j hj; simp [newRow, hj]
  · intro j
    apply time_mono hδ
    by_cases hj : j ∈ S <;> simp [newRow, hj]
  · have he : (∑ j ∈ S, roundUp δ (newRow j)) = δ * (z : ℝ) := by
      calc
        (∑ j ∈ S, roundUp δ (newRow j)) = ∑ j ∈ S, δ * (D j : ℝ) :=
          Finset.sum_congr rfl hround
        _ = δ * (z : ℝ) := by rw [← Finset.mul_sum, ← Int.cast_sum, hsum]
    rw [he]
    have hU : (∑ j ∈ S, roundUp δ (row j)) = δ * (↑(∑ j ∈ S, U j) : ℝ) := by
      simp only [Int.cast_sum, Finset.mul_sum, U, roundUp]
    rw [hU]
    rcases le_total (∑ j ∈ S, U j) m with h | h
    · have hc : δ * (↑(∑ j ∈ S, U j) : ℝ) ≤ δ * (m : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast h) hδ.le
      simp only [z, min_eq_left h, min_eq_left hc]
    · have hc : δ * (m : ℝ) ≤ δ * (↑(∑ j ∈ S, U j) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast h) hδ.le
      simp only [z, min_eq_right h, min_eq_right hc]

theorem solution {k : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (S T : Finset (Fin k)) (m : ℤ)
    (hfloor : (∑ _j ∈ S, roundUp δ a) ≤ δ * (m : ℝ))
    (himp : ∀ p : Fin k → ℝ, (∀ j, a ≤ p j ∧ p j ≤ b) →
      (∑ j ∈ S, roundUp δ (p j)) ≤ δ * (m : ℝ) →
      (∑ j ∈ T, roundUp δ (p j)) ≤ δ * (m : ℝ))
    (r : Fin k → ℝ) (hr : ∀ j, a ≤ r j ∧ r j ≤ b)
    (hrT : δ * (m : ℝ) < ∑ j ∈ T, roundUp δ (r j)) :
    (∑ j ∈ T, roundUp δ (r j)) ≤ ∑ j ∈ S, roundUp δ (r j) := by
  classical
  by_contra hbad
  have hbad' := lt_of_not_ge hbad
  let C := δ * (m : ℝ)
  let P := S ∩ T
  have hSP : S \ P = S \ T := by ext j; simp [P, Finset.mem_sdiff]
  have hTP : T \ P = T \ S := by ext j; simp [P, Finset.mem_sdiff]
  have splitS (w : Fin k → ℝ) :
      (∑ j ∈ S \ T, w j) + ∑ j ∈ P, w j = ∑ j ∈ S, w j := by
    rw [← hSP]
    exact Finset.sum_sdiff (show P ⊆ S from Finset.inter_subset_left)
  have splitT (w : Fin k → ℝ) :
      (∑ j ∈ T \ S, w j) + ∑ j ∈ P, w j = ∑ j ∈ T, w j := by
    rw [← hTP]
    exact Finset.sum_sdiff (show P ⊆ T from Finset.inter_subset_right)
  have hgain : (∑ _j ∈ S \ T, roundUp δ a) < ∑ _j ∈ T \ S, roundUp δ b := by
    have hl := Finset.sum_le_sum (s := S \ T) (fun j _ => time_mono hδ (hr j).1)
    have hu := Finset.sum_le_sum (s := T \ S) (fun j _ => time_mono hδ (hr j).2)
    have hs := splitS (fun j => roundUp δ (r j))
    have ht := splitT (fun j => roundUp δ (r j))
    linarith
  let q (j : Fin k) := if j ∈ T then b else a
  have hq (j : Fin k) : a ≤ q j ∧ q j ≤ b := by by_cases h : j ∈ T <;> simp [q, h, hab]
  have hqT : C < ∑ j ∈ T, roundUp δ (q j) := by
    refine hrT.trans_le (Finset.sum_le_sum (fun j hj => ?_))
    simpa [q, hj] using time_mono hδ (hr j).2
  by_cases hqS : (∑ j ∈ S, roundUp δ (q j)) ≤ C
  · exact (not_le_of_gt hqT) (himp q hq hqS)
  obtain ⟨p, hp, hpOut, hpMono, hpSum⟩ := cap_row hδ S q hq m hfloor
  have hpS : (∑ j ∈ S, roundUp δ (p j)) = C := hpSum.trans (min_eq_right (le_of_not_ge hqS))
  have hpSL : (∑ j ∈ S \ T, roundUp δ (p j)) = ∑ _j ∈ S \ T, roundUp δ a := by
    apply Finset.sum_congr rfl
    intro j hj
    have h := time_mono hδ (hp j).1
    have hh := hpMono j
    rw [show q j = a by simp [q, (Finset.mem_sdiff.1 hj).2]] at hh
    exact le_antisymm hh h
  have hpTG : (∑ j ∈ T \ S, roundUp δ (p j)) = ∑ _j ∈ T \ S, roundUp δ b := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hpOut j (Finset.mem_sdiff.1 hj).2]
    simp [q, (Finset.mem_sdiff.1 hj).1]
  have htP : (∑ j ∈ T, roundUp δ (p j)) ≤ C := himp p hp hpS.le
  have hs := splitS (fun j => roundUp δ (p j))
  have ht := splitT (fun j => roundUp δ (p j))
  rw [hpSL, hpS] at hs
  rw [hpTG] at ht
  linarith
