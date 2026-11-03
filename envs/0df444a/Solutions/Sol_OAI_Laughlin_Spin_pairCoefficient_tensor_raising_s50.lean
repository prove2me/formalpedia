-- Prove2me | solution 1 for OAI.Laughlin.Spin.pairCoefficient_tensor_raising_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:04:56.846515+00:00
-- url     : https://prove2.me/submissions/0f4229bb-7109-4423-9e64-9632c1d9bf9c

import Mathlib
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L014
import Definitions.Def_OAIQ050L015

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_PolynomialBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairCoefficient_choose (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairCoefficient Q p x y = if x.val+y.val = p+1 then
      ((x.val : ℝ)-(y.val : ℝ)) *
        Real.sqrt ((Q.choose x.val : ℝ)*(Q.choose y.val : ℝ) /
          (2*(Q : ℝ)*((2*Q-2).choose p : ℝ))) else 0 := by
  have hx : (x.val.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.val.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  unfold pairCoefficient
  split_ifs
  · have hr : (((Q.descFactorial x.val : ℝ)*(Q.descFactorial y.val : ℝ)*(p.factorial : ℝ)) /
        ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(x.val.factorial : ℝ)*(y.val.factorial : ℝ))) / 2 =
      (Q.choose x.val : ℝ)*(Q.choose y.val : ℝ)/(2*(Q : ℝ)*((2*Q-2).choose p : ℝ)) := by
        simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
        field_simp
    have hs := congrArg Real.sqrt hr
    rw [Real.sqrt_div (by positivity) (2 : ℝ)] at hs
    rw [← hs]
    ring
  · rfl

theorem pairCoefficient_polynomial_weight (Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (x y : Fin (Q+1)) :
    pairCoefficient Q p x y * Real.sqrt (Q.choose x.val : ℝ) *
      Real.sqrt (Q.choose y.val : ℝ) * Real.sqrt (2*(Q : ℝ)*((2*Q-2).choose p : ℝ)) =
        if x.val+y.val = p+1 then pairPolynomialCoefficient Q x.val y.val else 0 := by
  have hd : Real.sqrt (2*(Q : ℝ)*((2*Q-2).choose p : ℝ)) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hc : (0 : ℝ) < (2*Q-2).choose p := by exact_mod_cast Nat.choose_pos hp
    positivity
  rw [pairCoefficient_choose Q p hQ hp]
  split_ifs
  · rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
    unfold pairPolynomialCoefficient
    have hx := Real.sq_sqrt (show (0 : ℝ) ≤ Q.choose x.val by positivity)
    have hy := Real.sq_sqrt (show (0 : ℝ) ≤ Q.choose y.val by positivity)
    field_simp
    calc
      _ = ((x.val : ℝ)-(y.val : ℝ)) * (Real.sqrt (Q.choose x.val : ℝ))^2 *
        (Real.sqrt (Q.choose y.val : ℝ))^2 := by ring
      _ = _ := by rw [hx,hy]
  · simp

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

theorem normalizedPairState_eq_coefficients (Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (x y : Fin (Q+1)) :
    normalizedPairState Q p x.val y.val = pairCoefficient Q p x y *
      Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) := by
  unfold normalizedPairState rawPairState
  apply (div_eq_iff (ne_of_gt (pairNormalization_pos Q p hQ hp))).mpr
  exact (pairCoefficient_polynomial_weight Q p hQ hp x y).symm

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Highest2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem sqrt_choose_step (A p : ℕ) (hp : p < A) :
    ladder A p * Real.sqrt (A.choose (p+1) : ℝ) =
      (A-p : ℕ)*Real.sqrt (A.choose p : ℝ) := by
  have hc := choose_step_real A p (by omega)
  have he : (ladder A p * Real.sqrt (A.choose (p+1) : ℝ))^2 =
      ((A-p : ℕ)*Real.sqrt (A.choose p : ℝ))^2 := by
    unfold ladder
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    nlinarith [hc]
  have h₁ : 0 ≤ ladder A p * Real.sqrt (A.choose (p+1) : ℝ) := by
    exact mul_nonneg (le_of_lt (ladder_pos A p hp)) (Real.sqrt_nonneg _)
  have h₂ : 0 ≤ (A-p : ℕ)*Real.sqrt (A.choose p : ℝ) := by positivity
  nlinarith

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_PolynomialRaising
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairPolynomialCoefficient_raising (Q i j : ℕ) (hi : i ≤ Q) (hj : j ≤ Q) :
    ((i : ℝ)+1)*pairPolynomialCoefficient Q (i+1) j +
      ((j : ℝ)+1)*pairPolynomialCoefficient Q i (j+1) =
    (2*(Q : ℝ)-i-j-1)*pairPolynomialCoefficient Q i j := by
  have hx := Spin.choose_step_real Q i hi
  have hy := Spin.choose_step_real Q j hj
  rw [Nat.cast_sub hi] at hx
  rw [Nat.cast_sub hj] at hy
  unfold pairPolynomialCoefficient
  push_cast
  linear_combination
    ((i : ℝ)+1-j)*(Q.choose j : ℝ)*hx +
    ((i : ℝ)-j-1)*(Q.choose i : ℝ)*hy

theorem rawPairState_raising (Q p i j : ℕ) (hi : i ≤ Q) (hj : j ≤ Q) :
    raisePair (rawPairState Q (p+1)) i j =
      (2*(Q : ℝ)-2-p)*rawPairState Q p i j := by
  have hs : i+1+j = p+1+1 ↔ i+j=p+1 := by omega
  have ht : i+(j+1) = p+1+1 ↔ i+j=p+1 := by omega
  unfold raisePair rawPairState
  by_cases h : i+j=p+1
  · rw [ite_eq_left (hs.mpr h),ite_eq_left (ht.mpr h),ite_eq_left h]
    have hc : (i : ℝ)+j = (p : ℝ)+1 := by exact_mod_cast h
    rw [pairPolynomialCoefficient_raising Q i j hi hj]
    congr 1
    linarith
  · simp only [ite_eq_right h,ite_eq_right (mt hs.mp h),ite_eq_right (mt ht.mp h),mul_zero,add_zero]

theorem pairNormalization_raising_ratio (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2) :
    (2*(Q : ℝ)-2-p)/pairNormalization Q (p+1) =
      Spin.ladder (2*Q-2) p / pairNormalization Q p := by
  have h := Spin.sqrt_choose_step (2*Q-2) p hp
  have hc : ((2*Q-2-p : ℕ) : ℝ) = 2*(Q : ℝ)-2-p := by
    rw [Nat.cast_sub (by omega : p ≤ 2*Q-2),Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast; ring
  rw [hc] at h
  have hn₀ := ne_of_gt (pairNormalization_pos Q p hQ (by omega))
  have hn₁ := ne_of_gt (pairNormalization_pos Q (p+1) hQ (by omega))
  apply (div_eq_div_iff hn₁ hn₀).mpr
  unfold pairNormalization
  simp only [Real.sqrt_mul (by positivity : 0 ≤ 2*(Q : ℝ))]
  linear_combination -(Real.sqrt (2*(Q : ℝ)))*h

theorem normalizedPairState_raising (Q p i j : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
    (hi : i ≤ Q) (hj : j ≤ Q) :
    raisePair (normalizedPairState Q (p+1)) i j =
      Spin.ladder (2*Q-2) p * normalizedPairState Q p i j := by
  have hdiv : raisePair (normalizedPairState Q (p+1)) i j =
      raisePair (rawPairState Q (p+1)) i j / pairNormalization Q (p+1) := by
    unfold normalizedPairState raisePair
    ring
  rw [hdiv,rawPairState_raising Q p i j hi hj]
  unfold normalizedPairState
  calc
    _ = ((2*(Q : ℝ)-2-p)/pairNormalization Q (p+1))*rawPairState Q p i j := by ring
    _ = _ := by rw [pairNormalization_raising_ratio Q p hQ hp]; ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_TensorRaise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem ladder_weight_next (Q : ℕ) (x : Fin (Q+1)) (hx : x.val < Q) :
    ladder Q x.val*Real.sqrt (Q.choose x.val : ℝ) =
      ((x.val : ℝ)+1)*Real.sqrt (Q.choose (x.val+1) : ℝ) := by
  have h₀ : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have h₁ : Real.sqrt (Q.choose (x.val+1) : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val+1 ≤ Q)
  exact (div_eq_div_iff h₁ h₀).mp (ladder_div_sqrt_choose Q x.val hx)

theorem normalizedPairState_out_left (Q p i j : ℕ) (hi : Q < i) :
    normalizedPairState Q p i j = 0 := by
  simp [normalizedPairState,rawPairState,pairPolynomialCoefficient,Nat.choose_eq_zero_of_lt hi]

theorem normalizedPairState_out_right (Q p i j : ℕ) (hj : Q < j) :
    normalizedPairState Q p i j = 0 := by
  simp [normalizedPairState,rawPairState,pairPolynomialCoefficient,Nat.choose_eq_zero_of_lt hj]

theorem pairTensorRaise_weight (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorRaise Q p x y * Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      raisePair (normalizedPairState Q p) x.val y.val := by
  have hl :
      (if h : x.val < Q then ladder Q x.val*pairCoefficient Q p ⟨x.val+1,by omega⟩ y else 0) *
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      ((x.val : ℝ)+1)*normalizedPairState Q p (x.val+1) y.val := by
    by_cases hx : x.val < Q
    · rw [dite_eq_left hx,normalizedPairState_eq_coefficients Q p hQ hp ⟨x.val+1,by omega⟩ y]
      calc
        _ = pairCoefficient Q p ⟨x.val+1,by omega⟩ y * Real.sqrt (Q.choose y.val : ℝ)*
          (ladder Q x.val*Real.sqrt (Q.choose x.val : ℝ)) := by ring
        _ = _ := by rw [ladder_weight_next Q x hx]; ring
    · rw [dite_eq_right hx,normalizedPairState_out_left Q p (x.val+1) y.val (by omega)]
      ring
  have hr :
      (if h : y.val < Q then ladder Q y.val*pairCoefficient Q p x ⟨y.val+1,by omega⟩ else 0) *
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      ((y.val : ℝ)+1)*normalizedPairState Q p x.val (y.val+1) := by
    by_cases hy : y.val < Q
    · rw [dite_eq_left hy,normalizedPairState_eq_coefficients Q p hQ hp x ⟨y.val+1,by omega⟩]
      calc
        _ = pairCoefficient Q p x ⟨y.val+1,by omega⟩ * Real.sqrt (Q.choose x.val : ℝ)*
          (ladder Q y.val*Real.sqrt (Q.choose y.val : ℝ)) := by ring
        _ = _ := by rw [ladder_weight_next Q y hy]; ring
    · rw [dite_eq_right hy,normalizedPairState_out_right Q p x.val (y.val+1) (by omega)]
      ring
  unfold pairTensorRaise raisePair
  rw [add_mul,add_mul,hl,hr]

theorem pairCoefficient_tensor_raising_s50_oai (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorRaise Q (p+1) x y = ladder (2*Q-2) p * pairCoefficient Q p x y := by
  have hx : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have hy : Real.sqrt (Q.choose y.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : y.val ≤ Q)
  apply (mul_right_cancel₀ hy)
  apply (mul_right_cancel₀ hx)
  have he := pairTensorRaise_weight Q (p+1) hQ (by omega) x y
  rw [normalizedPairState_raising Q p x.val y.val hQ hp (by omega) (by omega),
    normalizedPairState_eq_coefficients Q p hQ (by omega) x y] at he
  linear_combination he

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.pairCoefficient_tensor_raising_s50_oai := @OAI.Laughlin.Spin.pairCoefficient_tensor_raising_s50_oai
