-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:57:50.874009+00:00
-- url     : https://prove2.me/submissions/b746231a-6ee8-4616-a7a6-94c745041927

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI.Laughlin.Certificate.S102YInt

lemma entry (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) (ht : t ≤ 16)
    (hT : e.1 + e.2.1 + (f.1 + f.2.1 - t) ≤ 24) :
    yEntry D r s t e f = (yEntryIntegral D r s t e f : ℚ) / arithmeticScale := by
  obtain ⟨p, j, a⟩ := e
  obtain ⟨q, l, b⟩ := f
  simp only at hT
  unfold yEntry yEntryIntegral arithmeticScale
  simp only
  split_ifs with hD
  · set T := p + j + (q + l - t) with hTdef
    have hTD : T - D ≤ 24 := by omega
    have hfac : ((Nat.factorial (T - D) : ℕ) : ℚ) * ((24 : ℕ).descFactorial (24 - (T - D)) : ℚ)
        = (Nat.factorial 24 : ℚ) := by
      have := Nat.factorial_mul_descFactorial (show 24 - (T - D) ≤ 24 by omega)
      rw [show 24 - (24 - (T - D)) = T - D by omega] at this
      exact_mod_cast this
    have hpos : (0:ℤ) ≤ 1 - 2 * (T : ℤ) + p + q - t + ((r + s) / 2 : ℕ) + 64 := by
      have : (T : ℤ) ≤ 24 := by exact_mod_cast hT
      have : (t : ℤ) ≤ 16 := by exact_mod_cast ht
      have : (0:ℤ) ≤ ((r + s) / 2 : ℕ) := by positivity
      omega
    rw [show (65 - 2 * (T : ℤ) + p + q - t + ((r + s) / 2 : ℕ)) =
      1 - 2 * (T : ℤ) + p + q - t + ((r + s) / 2 : ℕ) + 64 by ring]
    generalize 1 - 2 * (T : ℤ) + p + q - t + ((r + s) / 2 : ℕ) = z at hpos ⊢
    have hpow : (((2 : ℤ) ^ (z + 64).toNat : ℤ) : ℚ) = (2 : ℚ) ^ z * 2 ^ 64 := by
      rw [Int.cast_pow, Int.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg hpos,
        show (2:ℚ)^(64:ℕ) = (2:ℚ)^(64:ℤ) by norm_cast, ← zpow_add₀ (by norm_num)]
    have h24 : (Nat.factorial (T - D) : ℚ) ≠ 0 := by positivity
    rw [Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul,
      Int.cast_mul, Int.cast_mul, hpow, ← hfac]
    push_cast
    field_simp
  · simp

lemma sum_div {α : Type*} (L : List α) (g : α → ℤ) (c : ℚ) :
    ((L.map g).sum : ℚ) / c = (L.map (fun x => (g x : ℚ) / c)).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [add_div, ← ih]

end OAI.Laughlin.Certificate.S102YInt

open OAI.Laughlin.Certificate in
theorem solution (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (ht : row.1 ≤ 16)
    (hT : ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24) :
    yRow D r s row = (yRowIntegral D r s row : ℚ) / arithmeticScale := by
  unfold yRow yRowIntegral
  rw [S102YInt.sum_div]
  refine congrArg List.sum (List.map_congr_left fun e he => ?_)
  rw [S102YInt.sum_div]
  exact congrArg List.sum (List.map_congr_left fun f hf => S102YInt.entry _ _ _ _ _ _ ht (hT e he f hf))

