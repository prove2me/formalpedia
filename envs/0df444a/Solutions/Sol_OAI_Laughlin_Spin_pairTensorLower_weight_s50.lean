-- Prove2me | solution 1 for OAI.Laughlin.Spin.pairTensorLower_weight_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:06:25.294078+00:00
-- url     : https://prove2.me/submissions/bf7eb78e-9db5-4b77-9704-b095a244c04e

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_TensorLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem ladder_weight_previous (Q : ℕ) (x : Fin (Q+1)) (hx : 0 < x.val) :
    ladder Q (x.val-1)*Real.sqrt (Q.choose x.val : ℝ) =
      ((Q : ℝ)-x.val+1)*Real.sqrt (Q.choose (x.val-1) : ℝ) := by
  have h := sqrt_choose_step Q (x.val-1) (by omega)
  rw [show x.val-1+1=x.val by omega] at h
  have hc : ((Q-(x.val-1) : ℕ) : ℝ) = (Q : ℝ)-x.val+1 := by
    rw [Nat.cast_sub (by omega : x.val-1 ≤ Q),Nat.cast_sub (by omega : 1 ≤ x.val)]
    push_cast; ring
  rwa [hc] at h

theorem pairTensorLower_weight_s50_oai (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorLower Q p x y * Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      lowerPair Q (normalizedPairState Q p) x.val y.val := by
  have hl :
      (if h : 0 < x.val then ladder Q (x.val-1)*pairCoefficient Q p ⟨x.val-1,by omega⟩ y else 0) *
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      (if 0 < x.val then ((Q : ℝ)-x.val+1)*normalizedPairState Q p (x.val-1) y.val else 0) := by
    by_cases hx : 0 < x.val
    · rw [dite_eq_left hx,ite_eq_left hx,normalizedPairState_eq_coefficients Q p hQ hp ⟨x.val-1,by omega⟩ y]
      calc
        _ = pairCoefficient Q p ⟨x.val-1,by omega⟩ y * Real.sqrt (Q.choose y.val : ℝ)*
          (ladder Q (x.val-1)*Real.sqrt (Q.choose x.val : ℝ)) := by ring
        _ = _ := by rw [ladder_weight_previous Q x hx]; ring
    · simp only [dite_eq_right hx,ite_eq_right hx,zero_mul]
  have hr :
      (if h : 0 < y.val then ladder Q (y.val-1)*pairCoefficient Q p x ⟨y.val-1,by omega⟩ else 0) *
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      (if 0 < y.val then ((Q : ℝ)-y.val+1)*normalizedPairState Q p x.val (y.val-1) else 0) := by
    by_cases hy : 0 < y.val
    · rw [dite_eq_left hy,ite_eq_left hy,normalizedPairState_eq_coefficients Q p hQ hp x ⟨y.val-1,by omega⟩]
      calc
        _ = pairCoefficient Q p x ⟨y.val-1,by omega⟩ * Real.sqrt (Q.choose x.val : ℝ)*
          (ladder Q (y.val-1)*Real.sqrt (Q.choose y.val : ℝ)) := by ring
        _ = _ := by rw [ladder_weight_previous Q y hy]; ring
    · simp only [dite_eq_right hy,ite_eq_right hy,zero_mul]
  unfold pairTensorLower lowerPair
  rw [add_mul,add_mul,hl,hr]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.pairTensorLower_weight_s50_oai := @OAI.Laughlin.Spin.pairTensorLower_weight_s50_oai
