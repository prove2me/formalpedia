-- Prove2me | solution 1 for NoSignalPA.chsh_tensor_entry
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:41:32.354388+00:00
-- url     : https://prove2.me/submissions/c38965f6-5379-4312-b300-b737994f3aab

import Mathlib
import Definitions.Def_NoSignalPA_chshPow
import Definitions.Def_NoSignalPA_ones

namespace NoSignalPAChshAux

/-- `2^{-5/2} = 1/(4√2)`. -/
lemma two_rpow_neg_five_halves : (2 : ℝ) ^ (-(5 : ℝ) / 2) = 1 / (4 * Real.sqrt 2) := by
  have h : (2 : ℝ) ^ ((5 : ℝ) / 2) = 4 * Real.sqrt 2 := by
    rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.sqrt_eq_rpow]
    norm_num
  rw [neg_div, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), h, one_div]

/-- One system: `CHSH(a, b, x, y) = 2^{-5/2} · 5^{[a ⊕ b ⊕ xy]}`. -/
lemma chshCoef_eq (a b x y : Bool) :
    NoSignalPA.chshCoef a b x y =
      (2 : ℝ) ^ (-(5 : ℝ) / 2) * 5 ^ (if xor (xor a b) (x && y) then 1 else 0) := by
  rw [two_rpow_neg_five_halves]
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp [NoSignalPA.chshCoef, NoSignalPA.cell]

end NoSignalPAChshAux

open NoSignalPAChshAux in
theorem solution {Nr : ℕ} (a b x y : NoSignalPA.Str Nr) :
    NoSignalPA.chshPow a b x y
      = (2 : ℝ) ^ (-(5 * (Nr : ℝ)) / 2)
          * 5 ^ NoSignalPA.ones (fun i => xor (xor (a i) (b i)) (x i && y i)) := by
  unfold NoSignalPA.chshPow
  simp only [chshCoef_eq, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  · rw [Finset.prod_pow_eq_pow_sum, NoSignalPA.ones]
    congr 1
    rw [Finset.card_filter]
