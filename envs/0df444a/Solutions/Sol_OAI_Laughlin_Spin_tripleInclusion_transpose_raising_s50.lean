-- Prove2me | solution 1 for OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:44:47.40123+00:00
-- url     : https://prove2.me/submissions/b3d4dae2-f862-4912-b684-76b8f13ae256

import Mathlib
import Definitions.Def_OAIQ050L015
import Definitions.Def_OAIQ050L018
import Definitions.Def_OAIQ050L019
import Theorems.Thm_OAI_Laughlin_Spin_pairCoefficient_tensor_lowering_s50
import Theorems.Thm_OAI_Laughlin_Spin_pairTensorLower_weight_s50

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

theorem lowerPair_div (Q : ℕ) (f : ℕ → ℕ → ℝ) (d : ℝ) (i j : ℕ) :
    lowerPair Q (fun i j => f i j / d) i j = lowerPair Q f i j / d := by
  unfold lowerPair
  split_ifs <;> ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_TensorBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem rawPairState_past_lowest (Q i j : ℕ) (hQ : 0 < Q)
    (hi : i ≤ Q) (hj : j ≤ Q) :
    rawPairState Q (2*Q-2+1) i j = 0 := by
  by_cases h : i+j=2*Q-2+1+1
  · have he : i=j := by omega
    simp [rawPairState,pairPolynomialCoefficient,he]
  · simp [rawPairState,h]

theorem normalizedPairState_lowest (Q i j : ℕ) (hQ : 0 < Q)
    (hi : i ≤ Q) (hj : j ≤ Q) :
    lowerPair Q (normalizedPairState Q (2*Q-2)) i j = 0 := by
  unfold normalizedPairState
  rw [lowerPair_div,rawPairState_lowering Q (2*Q-2) i j hi hj,
    rawPairState_past_lowest Q i j hQ hi hj]
  simp

theorem pairCoefficient_tensor_lowest (Q : ℕ) (hQ : 0 < Q)
    (x y : Fin (Q+1)) : pairTensorLower Q (2*Q-2) x y = 0 := by
  have he := pairTensorLower_weight_s50 Q (2*Q-2) hQ (by omega) x y
  rw [normalizedPairState_lowest Q x.val y.val hQ (by omega) (by omega)] at he
  have hx : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have hy : Real.sqrt (Q.choose y.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : y.val ≤ Q)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hy)).resolve_right hx

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_LadderIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairInclusion_lowering (Q : ℕ) (hQ : 0 < Q) :
    (totalRaise Q Q)ᵀ * pairInclusion Q = pairInclusion Q * (raiseMatrix (2*Q-2))ᵀ := by
  ext i p
  change (∑ j, totalRaise Q Q j i*pairCoefficient Q p.val j.1 j.2) =
    ∑ k, pairCoefficient Q k.val i.1 i.2 * raiseMatrix (2*Q-2) p k
  conv_rhs => simp only [mul_comm (pairCoefficient Q _ _ _)]
  rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column,raiseMatrix_row]
  have heq :
      (if h : 0 < i.1.val then pairCoefficient Q p.val ⟨i.1.val-1,by omega⟩ i.2 *
        ladder Q (i.1.val-1) else 0) +
      (if h : 0 < i.2.val then pairCoefficient Q p.val i.1 ⟨i.2.val-1,by omega⟩ *
        ladder Q (i.2.val-1) else 0) = pairTensorLower Q p.val i.1 i.2 := by
    unfold pairTensorLower
    split_ifs <;> ring
  rw [heq]
  by_cases hp : p.val < 2*Q-2
  · rw [dite_eq_left hp,pairCoefficient_tensor_lowering_s50 Q p.val hQ hp]
  · rw [dite_eq_right hp]
    have hz : p.val=2*Q-2 := by omega
    rw [hz,pairCoefficient_tensor_lowest Q hQ]

theorem pairInclusion_transpose_raising (Q : ℕ) (hQ : 0 < Q) :
    (pairInclusion Q)ᵀ * totalRaise Q Q = raiseMatrix (2*Q-2) * (pairInclusion Q)ᵀ := by
  have h := congrArg Matrix.transpose (pairInclusion_lowering Q hQ)
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using h

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TripleLadderIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem tripleInclusion_transpose (Q : ℕ) :
    (tripleInclusion Q)ᵀ = (pairInclusion Q)ᵀ ⊗ₖ (1 : Matrix (Orbital Q) (Orbital Q) ℝ) := by
  ext i j
  simp [tripleInclusion,Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]

theorem tripleInclusion_transpose_raising_s50_oai (Q : ℕ) (hQ : 0 < Q) :
    (tripleInclusion Q)ᵀ * tripleRaise Q = totalRaise (2*Q-2) Q * (tripleInclusion Q)ᵀ := by
  rw [tripleInclusion_transpose,totalRaise_kronecker]
  unfold tripleRaise
  simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_kronecker_mul,
    Matrix.mul_one,Matrix.one_mul,pairInclusion_transpose_raising Q hQ]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50_oai := @OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50_oai
