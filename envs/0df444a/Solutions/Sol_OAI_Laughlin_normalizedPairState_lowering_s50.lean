-- Prove2me | solution 1 for OAI.Laughlin.normalizedPairState_lowering_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:12:01.326521+00:00
-- url     : https://prove2.me/submissions/44665e42-1121-42ca-b985-5c9766c05500

import Mathlib
import Definitions.Def_OAIQ050L015

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_LoweringAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem choose_lowering (Q i : ℕ) (hi : 0 < i) (hiQ : i ≤ Q+1) :
    ((Q : ℝ)-(i : ℝ)+1) * (Q.choose (i-1) : ℝ) =
      (i : ℝ) * (Q.choose i : ℝ) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  have hk : k ≤ Q := by omega
  have h := Nat.choose_succ_right_eq Q k
  have hc := congrArg (fun x : ℕ => (x : ℝ)) h
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk] at hc
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  nlinarith only [hc]

theorem pairPolynomialCoefficient_lowering (Q i j : ℕ)
    (hiQ : i ≤ Q) (hjQ : j ≤ Q) :
    (if 0 < i then ((Q : ℝ)-(i : ℝ)+1)*pairPolynomialCoefficient Q (i-1) j else 0) +
    (if 0 < j then ((Q : ℝ)-(j : ℝ)+1)*pairPolynomialCoefficient Q i (j-1) else 0) =
      ((i : ℝ)+(j : ℝ)-1)*pairPolynomialCoefficient Q i j := by
  have left : (if 0 < i then ((Q : ℝ)-(i : ℝ)+1)*pairPolynomialCoefficient Q (i-1) j else 0) =
      (i : ℝ)*((i : ℝ)-1-(j : ℝ))*(Q.choose i : ℝ)*(Q.choose j : ℝ) := by
    by_cases hi : 0 < i
    · rw [ite_eq_left hi]
      unfold pairPolynomialCoefficient
      rw [Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one]
      calc
        _ = ((i : ℝ)-1-(j : ℝ))*(Q.choose j : ℝ)*
          (((Q : ℝ)-(i : ℝ)+1)*(Q.choose (i-1) : ℝ)) := by ring
        _ = _ := by rw [choose_lowering Q i hi (by omega)]; ring
    · have hz : i = 0 := by omega
      simp [hz]
  have right : (if 0 < j then ((Q : ℝ)-(j : ℝ)+1)*pairPolynomialCoefficient Q i (j-1) else 0) =
      (j : ℝ)*((i : ℝ)-((j : ℝ)-1))*(Q.choose i : ℝ)*(Q.choose j : ℝ) := by
    by_cases hj : 0 < j
    · rw [ite_eq_left hj]
      unfold pairPolynomialCoefficient
      rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
      calc
        _ = ((i : ℝ)-((j : ℝ)-1))*(Q.choose i : ℝ)*
          (((Q : ℝ)-(j : ℝ)+1)*(Q.choose (j-1) : ℝ)) := by ring
        _ = _ := by rw [choose_lowering Q j hj (by omega)]; ring
    · have hz : j = 0 := by omega
      simp [hz]
  rw [left, right]
  unfold pairPolynomialCoefficient
  ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_PolynomialLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem rawPairState_lowering (Q p i j : ℕ) (hiQ : i ≤ Q) (hjQ : j ≤ Q) :
    lowerPair Q (rawPairState Q p) i j = (p+1 : ℕ)*rawPairState Q (p+1) i j := by
  by_cases h : i+j = p+2
  · have hx : 0 < i → i-1+j = p+1 := by omega
    have hy : 0 < j → i+(j-1) = p+1 := by omega
    have hr : ((i : ℝ)+(j : ℝ)-1) = (p+1 : ℕ) := by
      have hc := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast at hc ⊢
      linarith
    have ha := pairPolynomialCoefficient_lowering Q i j hiQ hjQ
    rw [hr] at ha
    by_cases hi : 0 < i <;> by_cases hj : 0 < j
    · simpa [lowerPair, rawPairState, h, hx hi, hy hj, hi, hj, Nat.add_assoc] using ha
    · simpa [lowerPair, rawPairState, h, hx hi, hi, hj, Nat.add_assoc] using ha
    · simpa [lowerPair, rawPairState, h, hy hj, hi, hj, Nat.add_assoc] using ha
    · simpa [lowerPair, rawPairState, h, hi, hj, Nat.add_assoc] using ha
  · have hx : 0 < i → i-1+j ≠ p+1 := by omega
    have hy : 0 < j → i+(j-1) ≠ p+1 := by omega
    by_cases hi : 0 < i <;> by_cases hj : 0 < j
    · simp [lowerPair, rawPairState, h, hx hi, hy hj, hi, hj, Nat.add_assoc]
    · simp [lowerPair, rawPairState, h, hx hi, hi, hj, Nat.add_assoc]
    · simp [lowerPair, rawPairState, h, hy hj, hi, hj, Nat.add_assoc]
    · simp [lowerPair, rawPairState, h, hi, hj, Nat.add_assoc]

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_NormalizedLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairNormalization_pos (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2) :
    0 < pairNormalization Q p := by
  unfold pairNormalization
  apply Real.sqrt_pos.mpr
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hc : (0 : ℝ) < (2*Q-2).choose p := by exact_mod_cast Nat.choose_pos hp
  positivity

theorem pairNormalization_ratio (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2) :
    ((p : ℝ)+1) / pairNormalization Q p =
      Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ)) / pairNormalization Q (p+1) := by
  have hdn := pairNormalization_pos Q (p+1) hQ (by omega)
  have hd := pairNormalization_pos Q p hQ (by omega)
  apply (div_eq_div_iff (ne_of_gt hd) (ne_of_gt hdn)).mpr
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq (2*Q-2) p)
  push_cast at hc
  have he : (((p : ℝ)+1)*pairNormalization Q (p+1))^2 =
      (Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*pairNormalization Q p)^2 := by
    unfold pairNormalization
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    linear_combination (2*(Q : ℝ)*((p : ℝ)+1))*hc
  have hn₁ : 0 ≤ ((p : ℝ)+1)*pairNormalization Q (p+1) := by positivity
  have hn₂ : 0 ≤ Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*pairNormalization Q p := by positivity
  nlinarith only [he,hn₁,hn₂]

theorem lowerPair_div (Q : ℕ) (f : ℕ → ℕ → ℝ) (d : ℝ) (i j : ℕ) :
    lowerPair Q (fun i j => f i j / d) i j = lowerPair Q f i j / d := by
  unfold lowerPair
  split_ifs <;> ring

theorem normalizedPairState_lowering_s50_oai (Q p i j : ℕ) (hQ : 0 < Q)
    (hp : p < 2*Q-2) (hi : i ≤ Q) (hj : j ≤ Q) :
    lowerPair Q (normalizedPairState Q p) i j =
      Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*normalizedPairState Q (p+1) i j := by
  unfold normalizedPairState
  rw [lowerPair_div, rawPairState_lowering Q p i j hi hj]
  push_cast
  calc
    _ = (((p : ℝ)+1)/pairNormalization Q p)*rawPairState Q (p+1) i j := by ring
    _ = _ := by rw [pairNormalization_ratio Q p hQ hp]; ring

end Laughlin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.normalizedPairState_lowering_s50_oai := @OAI.Laughlin.normalizedPairState_lowering_s50_oai
