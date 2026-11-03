-- Prove2me | solution 1 for OAI.Laughlin.Spin.pairInclusion_raising_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:06:24.287229+00:00
-- url     : https://prove2.me/submissions/497b2a9a-73a0-4221-ab46-aac6b7458ad9

import Mathlib
import Definitions.Def_OAIQ050L015
import Definitions.Def_OAIQ050L018
import Definitions.Def_OAIQ050L019
import Theorems.Thm_OAI_Laughlin_Spin_pairCoefficient_tensor_raising_s50

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

end Laughlin.Spin

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

theorem rawPairState_highest (Q i j : ℕ) :
    raisePair (rawPairState Q 0) i j = 0 := by
  by_cases h : i+j=0
  · have hi : i=0 := by omega
    have hj : j=0 := by omega
    simp [hi,hj,raisePair,rawPairState,pairPolynomialCoefficient]
  · have hi : i+1+j ≠ 0+1 := by omega
    have hj : i+(j+1) ≠ 0+1 := by omega
    simp [raisePair,rawPairState,hi,hj]

theorem normalizedPairState_highest (Q i j : ℕ) :
    raisePair (normalizedPairState Q 0) i j = 0 := by
  have he : raisePair (normalizedPairState Q 0) i j =
      raisePair (rawPairState Q 0) i j / pairNormalization Q 0 := by
    unfold raisePair normalizedPairState; ring
  rw [he,rawPairState_highest,zero_div]

theorem pairCoefficient_tensor_highest (Q : ℕ) (hQ : 0 < Q)
    (x y : Fin (Q+1)) : pairTensorRaise Q 0 x y = 0 := by
  have he := pairTensorRaise_weight Q 0 hQ (by omega) x y
  rw [normalizedPairState_highest] at he
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

theorem pairInclusion_raising_s50_oai (Q : ℕ) (hQ : 0 < Q) :
    totalRaise Q Q * pairInclusion Q = pairInclusion Q * raiseMatrix (2*Q-2) := by
  ext i p
  change (∑ j, totalRaise Q Q i j*pairCoefficient Q p.val j.1 j.2) =
    ∑ k, pairCoefficient Q k.val i.1 i.2 * raiseMatrix (2*Q-2) k p
  rw [totalRaise_apply,raiseMatrix_row,raiseMatrix_row,raiseMatrix_column]
  change pairTensorRaise Q p.val i.1 i.2 = _
  by_cases hp : 0 < p.val
  · rw [dite_eq_left hp]
    have he := pairCoefficient_tensor_raising_s50 Q (p.val-1) hQ (by omega) i.1 i.2
    rw [show p.val-1+1=p.val by omega] at he
    simpa only [mul_comm] using he
  · rw [dite_eq_right hp]
    have hz : p.val=0 := by omega
    rw [hz,pairCoefficient_tensor_highest Q hQ]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.pairInclusion_raising_s50_oai := @OAI.Laughlin.Spin.pairInclusion_raising_s50_oai
