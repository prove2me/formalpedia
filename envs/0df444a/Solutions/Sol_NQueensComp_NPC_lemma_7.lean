-- Prove2me | solution 1 for NQueensComp.NPC.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:43:13.491798+00:00
-- url     : https://prove2.me/submissions/51d3d914-6f37-4da6-b1bd-2054a101bd4b

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

open NQueensComp.NPC

/-- Rows of `Aₙ` are injective: `2i mod n = 2j mod n` forces `i = j` for `i, j < n`. -/
theorem row_inj (n : ℕ) (cop2 : Nat.gcd n 2 = 1) (i j : ℕ) (hi : i < n) (hj : j < n) (h : 2 * i % n = 2 * j % n) : i = j := by
  have h1 : 2 * i ≡ 2 * j [MOD n] := h
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime cop2 h1) hi hj

/-- `i + (2i mod n) ≡ j + (2j mod n) (mod n)` forces `i = j`. -/
theorem sum_inj (n : ℕ) (cop3 : Nat.gcd n 3 = 1) (i j : ℕ) (hi : i < n) (hj : j < n)
    (h : i + 2 * i % n ≡ j + 2 * j % n [MOD n]) : i = j := by
  have h1 : i + 2 * i % n ≡ 3 * i [MOD n] := by
    have := Nat.ModEq.add_left i (Nat.mod_modEq (2 * i) n)
    exact this.trans (by rw [show i + 2 * i = 3 * i by ring])
  have h2 : j + 2 * j % n ≡ 3 * j [MOD n] := by
    have := Nat.ModEq.add_left j (Nat.mod_modEq (2 * j) n)
    exact this.trans (by rw [show j + 2 * j = 3 * j by ring])
  have h3 : 3 * i ≡ 3 * j [MOD n] := h1.symm.trans (h.trans h2)
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime cop3 h3) hi hj

/-- `(2i mod n) ≡ 2i (mod n)` in `ℤ`. -/
theorem mod_cast_modEq (n : ℕ) (i : ℕ) : ((2 * i % n : ℕ) : ℤ) ≡ 2 * (i : ℤ) [ZMOD (n : ℤ)] := by
  have := Int.natCast_modEq_iff.mpr (Nat.mod_modEq (2 * i) n)
  push_cast at this
  exact this

/-- `i − (2i mod n) ≡ j − (2j mod n) (mod n)` forces `i = j`. -/
theorem diffA_inj (n : ℕ) (i j : ℕ) (hi : i < n) (hj : j < n)
    (h : (i : ℤ) - ((2 * i % n : ℕ) : ℤ) ≡ (j : ℤ) - ((2 * j % n : ℕ) : ℤ) [ZMOD (n : ℤ)]) :
    i = j := by
  have h1 : (i : ℤ) - ((2 * i % n : ℕ) : ℤ) ≡ -(i : ℤ) [ZMOD (n : ℤ)] := by
    have := Int.ModEq.sub_left (i : ℤ) (mod_cast_modEq n i)
    exact this.trans (by rw [show (i : ℤ) - 2 * i = -i by ring])
  have h2 : (j : ℤ) - ((2 * j % n : ℕ) : ℤ) ≡ -(j : ℤ) [ZMOD (n : ℤ)] := by
    have := Int.ModEq.sub_left (j : ℤ) (mod_cast_modEq n j)
    exact this.trans (by rw [show (j : ℤ) - 2 * j = -j by ring])
  have h3 : -(i : ℤ) ≡ -(j : ℤ) [ZMOD (n : ℤ)] := h1.symm.trans (h.trans h2)
  have h4 : (i : ℤ) ≡ (j : ℤ) [ZMOD (n : ℤ)] := by simpa using h3.neg
  exact Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.mp h4) hi hj

/-- `(2i mod n) − i ≡ (2j mod n) − j (mod n)` forces `i = j`. -/
theorem diffB_inj (n : ℕ) (i j : ℕ) (hi : i < n) (hj : j < n)
    (h : ((2 * i % n : ℕ) : ℤ) - (i : ℤ) ≡ ((2 * j % n : ℕ) : ℤ) - (j : ℤ) [ZMOD (n : ℤ)]) :
    i = j := by
  have h1 : ((2 * i % n : ℕ) : ℤ) - (i : ℤ) ≡ (i : ℤ) [ZMOD (n : ℤ)] := by
    have := Int.ModEq.sub_right (i : ℤ) (mod_cast_modEq n i)
    exact this.trans (by rw [show 2 * (i : ℤ) - i = i by ring])
  have h2 : ((2 * j % n : ℕ) : ℤ) - (j : ℤ) ≡ (j : ℤ) [ZMOD (n : ℤ)] := by
    have := Int.ModEq.sub_right (j : ℤ) (mod_cast_modEq n j)
    exact this.trans (by rw [show 2 * (j : ℤ) - j = j by ring])
  have h4 : (i : ℤ) ≡ (j : ℤ) [ZMOD (n : ℤ)] := h1.symm.trans (h.trans h2)
  exact Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.mp h4) hi hj

/-- For `0 < i < n` (and `n` odd), `2(n − i) mod n = n − (2i mod n)`. -/
theorem key_reflect (n : ℕ) (cop2 : Nat.gcd n 2 = 1) (i : ℕ) (hi0 : 0 < i) (hi : i < n) : 2 * (n - i) % n = n - 2 * i % n := by
  have hdm := Nat.div_add_mod (2 * i) n
  have hr : 2 * i % n < n := Nat.mod_lt _ (by omega)
  have hr0 : 2 * i % n ≠ 0 := by
    intro h0
    have hdvd : n ∣ i * 2 := by rw [mul_comm]; exact Nat.dvd_of_mod_eq_zero h0
    have : n ∣ i := Nat.Coprime.dvd_of_dvd_mul_right cop2 hdvd
    have := Nat.le_of_dvd hi0 this
    omega
  have hq : 2 * i / n ≤ 1 := by
    by_contra hc
    push_neg at hc
    have : n * 2 ≤ n * (2 * i / n) := Nat.mul_le_mul_left n hc
    omega
  generalize 2 * i / n = q at hdm hq
  generalize 2 * i % n = r at hdm hr hr0 ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl
  · have : 2 * (n - i) = n + (n - r) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · have : 2 * (n - i) = n - r := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]

theorem solution (n : ℕ) (hn : n % 6 = 1 ∨ n % 6 = 5) :
    IsModularSol n (A n) ∧ IsModularSol n (B n) ∧
      (A n).image sumDiag = (B n).image sumDiag ∧
      (A n).image diffDiag = (B n).image diffDiag := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have cop2 : Nat.gcd n 2 = 1 := ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)).symm
  have cop3 : Nat.gcd n 3 = 1 := ((Nat.prime_three.coprime_iff_not_dvd).mpr (by omega)).symm
  have hmemA : ∀ q, q ∈ A n ↔ ∃ i < n, (i, 2 * i % n) = q := by
    intro q; simp [A]
  have hmemB : ∀ q, q ∈ B n ↔ ∃ i < n, (2 * i % n, i) = q := by
    intro q; simp [B]
  -- the two solutions
  have hA : IsModularSol n (A n) := by
    refine ⟨⟨hn1, ?_, ?_, ?_⟩, ?_⟩
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := (hmemA q).mp hq
      simp only [FitsOn, size, max_lt_iff]
      exact ⟨hi, Nat.mod_lt _ hn0⟩
    · rw [A, Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)]
      simp
    · intro q₁ h₁ q₂ h₂ hatt
      obtain ⟨i, hi, rfl⟩ := (hmemA q₁).mp h₁
      obtain ⟨j, hj, rfl⟩ := (hmemA q₂).mp h₂
      obtain ⟨hne, hl⟩ := hatt
      apply hne
      simp only [col, row, sumDiag, diffDiag] at hl
      have : i = j := by
        rcases hl with h | h | h | h
        · exact h
        · exact row_inj n cop2 i j hi hj h
        · exact sum_inj n cop3 i j hi hj (by rw [h])
        · exact diffA_inj n i j hi hj (by rw [h])
      rw [this]
    · intro q₁ h₁ q₂ h₂ hne
      obtain ⟨i, hi, rfl⟩ := (hmemA q₁).mp h₁
      obtain ⟨j, hj, rfl⟩ := (hmemA q₂).mp h₂
      simp only [sumDiag, diffDiag]
      constructor
      · intro h
        apply hne
        rw [sum_inj n cop3 i j hi hj (Int.natCast_modEq_iff.mp h)]
      · intro h
        apply hne
        rw [diffA_inj n i j hi hj h]
  have hB : IsModularSol n (B n) := by
    refine ⟨⟨hn1, ?_, ?_, ?_⟩, ?_⟩
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := (hmemB q).mp hq
      simp only [FitsOn, size, max_lt_iff]
      exact ⟨Nat.mod_lt _ hn0, hi⟩
    · rw [B, Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.snd h)]
      simp
    · intro q₁ h₁ q₂ h₂ hatt
      obtain ⟨i, hi, rfl⟩ := (hmemB q₁).mp h₁
      obtain ⟨j, hj, rfl⟩ := (hmemB q₂).mp h₂
      obtain ⟨hne, hl⟩ := hatt
      apply hne
      simp only [col, row, sumDiag, diffDiag] at hl
      have : i = j := by
        rcases hl with h | h | h | h
        · exact row_inj n cop2 i j hi hj h
        · exact h
        · exact sum_inj n cop3 i j hi hj (by rw [add_comm i, add_comm j, h])
        · exact diffB_inj n i j hi hj (by rw [h])
      rw [this]
    · intro q₁ h₁ q₂ h₂ hne
      obtain ⟨i, hi, rfl⟩ := (hmemB q₁).mp h₁
      obtain ⟨j, hj, rfl⟩ := (hmemB q₂).mp h₂
      simp only [sumDiag, diffDiag]
      constructor
      · intro h
        apply hne
        have h' : i + 2 * i % n ≡ j + 2 * j % n [MOD n] := by
          rw [add_comm i, add_comm j]; exact Int.natCast_modEq_iff.mp h
        rw [sum_inj n cop3 i j hi hj h']
      · intro h
        apply hne
        rw [diffB_inj n i j hi hj h]
  refine ⟨hA, hB, ?_, ?_⟩
  · rw [A, B, Finset.image_image, Finset.image_image]
    congr 1
    funext i
    simp [sumDiag, add_comm]
  · rw [A, B, Finset.image_image, Finset.image_image]
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Function.comp, diffDiag]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact ⟨0, hn0, by simp⟩
      · refine ⟨n - i, by omega, ?_⟩
        rw [key_reflect n cop2 i hi0 hi]
        have hr : 2 * i % n < n := Nat.mod_lt _ hn0
        push_cast [Nat.cast_sub hr.le, Nat.cast_sub hi.le]
        ring
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact ⟨0, hn0, by simp⟩
      · refine ⟨n - i, by omega, ?_⟩
        rw [key_reflect n cop2 i hi0 hi]
        have hr : 2 * i % n < n := Nat.mod_lt _ hn0
        push_cast [Nat.cast_sub hr.le, Nat.cast_sub hi.le]
        ring
