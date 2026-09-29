-- Prove2me | solution 1 for Maldacena1999.poincareEmbedding_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T12:10:01.474608+00:00
-- url     : https://prove2.me/submissions/53873b26-a6aa-46fb-87b7-f599e9a7f531

import Mathlib
import Definitions.Def_Maldacena1999_Defs

open Filter Topology

open Maldacena1999 in
lemma malda_sign_zero (p : ℕ) : ambientSign p 0 = -1 := by
  simp [ambientSign]

open Maldacena1999 in
lemma malda_sign_last (p : ℕ) : ambientSign p (Fin.last (p + 2)) = 1 := by
  simp [ambientSign]

open Maldacena1999 in
lemma malda_sign_mid (p : ℕ) (k : Fin (p + 1)) :
    ambientSign p k.castSucc.succ = if k.val = 0 then (-1 : ℝ) else 1 := by
  have h1 : (k.castSucc.succ : Fin (p + 3)).val = k.val + 1 := by simp
  unfold ambientSign
  rw [h1]
  by_cases hk : k.val = 0
  · rw [if_pos (by omega), if_pos hk]
  · rw [if_neg (by omega), if_neg hk]

open Maldacena1999 in
lemma malda_ambientForm_split (p : ℕ) (X : Fin (p + 3) → ℝ) :
    ambientForm p X = -X 0 ^ 2 + X (Fin.last (p + 2)) ^ 2 +
      ∑ k : Fin (p + 1), (if k.val = 0 then (-1 : ℝ) else 1) * X k.castSucc.succ ^ 2 := by
  unfold ambientForm
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last]
  simp only [malda_sign_zero, malda_sign_last, malda_sign_mid]
  ring

open Maldacena1999 in
lemma malda_pe_zero (p : ℕ) (R : ℝ) (q : ℝ × (Fin (p + 1) → ℝ)) :
    poincareEmbedding p R q 0 =
      (q.1 + (minkowskiForm p q.2 * q.1 / R ^ 2 + R ^ 2 / q.1)) / 2 := by
  simp [poincareEmbedding]

open Maldacena1999 in
lemma malda_pe_mid (p : ℕ) (R : ℝ) (q : ℝ × (Fin (p + 1) → ℝ)) (k : Fin (p + 1)) :
    poincareEmbedding p R q k.castSucc.succ = q.2 k * q.1 / R := by
  have hk : ¬ p < k.val := Nat.not_lt.2 k.is_le
  simp [poincareEmbedding, hk]

open Maldacena1999 in
lemma malda_pe_last (p : ℕ) (R : ℝ) (q : ℝ × (Fin (p + 1) → ℝ)) :
    poincareEmbedding p R q (Fin.last (p + 2)) =
      (q.1 - (minkowskiForm p q.2 * q.1 / R ^ 2 + R ^ 2 / q.1)) / 2 := by
  simp [poincareEmbedding]

open Maldacena1999 in
lemma malda_mink_scale (p : ℕ) (x : Fin (p + 1) → ℝ) (c : ℝ) :
    ∑ k : Fin (p + 1), (if k.val = 0 then (-1 : ℝ) else 1) * (x k * c) ^ 2 =
      minkowskiForm p x * c ^ 2 := by
  unfold minkowskiForm
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

open Maldacena1999 in
theorem solution (p : ℕ) (R : ℝ) (hR : 0 < R) :
    Set.BijOn (poincareEmbedding p R) {q | 0 < q.1}
      {X | X ∈ AdS p R ∧ 0 < X 0 + X (Fin.last (p + 2))} := by
  have hR0 : R ≠ 0 := hR.ne'
  have hsum : ∀ q : ℝ × (Fin (p + 1) → ℝ),
      poincareEmbedding p R q 0 + poincareEmbedding p R q (Fin.last (p + 2)) = q.1 := by
    intro q
    rw [malda_pe_zero, malda_pe_last]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    simp only [Set.mem_setOf_eq] at hq
    refine ⟨?_, ?_⟩
    · show ambientForm p _ = -R ^ 2
      rw [malda_ambientForm_split, malda_pe_zero, malda_pe_last]
      simp only [malda_pe_mid]
      have hm : ∑ k : Fin (p + 1), (if k.val = 0 then (-1 : ℝ) else 1) * (q.2 k * q.1 / R) ^ 2 =
          minkowskiForm p q.2 * (q.1 / R) ^ 2 := by
        rw [← malda_mink_scale]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
      rw [hm]
      have hq0 : q.1 ≠ 0 := hq.ne'
      field_simp
      try ring
    · rw [hsum q]
      exact hq
  · intro q hq q' hq' h
    simp only [Set.mem_setOf_eq] at hq hq'
    have hU : q.1 = q'.1 := by rw [← hsum q, ← hsum q', h]
    have hx : q.2 = q'.2 := by
      funext k
      have hk := congrFun h k.castSucc.succ
      rw [malda_pe_mid, malda_pe_mid, hU] at hk
      have hq0 : q'.1 ≠ 0 := hq'.ne'
      rw [mul_div_assoc, mul_div_assoc] at hk
      exact mul_right_cancel₀ (div_ne_zero hq0 hR0) hk
    exact Prod.ext hU hx
  · intro X hX
    obtain ⟨hA, hpos⟩ := hX
    have hA' : ambientForm p X = -R ^ 2 := hA
    rw [malda_ambientForm_split] at hA'
    have hU0 : X 0 + X (Fin.last (p + 2)) ≠ 0 := hpos.ne'
    refine ⟨(X 0 + X (Fin.last (p + 2)),
      fun k => X k.castSucc.succ * (R / (X 0 + X (Fin.last (p + 2))))), hpos, ?_⟩
    have hM : minkowskiForm p (fun k => X k.castSucc.succ * (R / (X 0 + X (Fin.last (p + 2))))) =
        (X 0 ^ 2 - X (Fin.last (p + 2)) ^ 2 - R ^ 2) * (R / (X 0 + X (Fin.last (p + 2)))) ^ 2 := by
      have hS : ∑ k : Fin (p + 1), (if k.val = 0 then (-1 : ℝ) else 1) * X k.castSucc.succ ^ 2 =
          X 0 ^ 2 - X (Fin.last (p + 2)) ^ 2 - R ^ 2 := by linarith
      unfold minkowskiForm
      rw [← hS, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      dsimp only
      ring
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [malda_pe_zero]
      simp only
      rw [hM]
      field_simp
      try ring
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [Fin.succ_last, malda_pe_last]
        simp only
        rw [hM]
        field_simp
        try ring
      · rw [malda_pe_mid]
        field_simp
