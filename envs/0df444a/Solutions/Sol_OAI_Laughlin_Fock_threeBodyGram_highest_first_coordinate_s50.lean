-- Prove2me | solution 1 for OAI.Laughlin.Fock.threeBodyGram_highest_first_coordinate_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:01:35.074997+00:00
-- url     : https://prove2.me/submissions/c80896bb-748b-459c-9851-bdce4fe18192

import Mathlib
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L013
import Definitions.Def_OAIQ050L014
import Theorems.Thm_OAI_Laughlin_Fock_threeBodyGramSlice_first_row_pos_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_HighestSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem highestRaw_zero (A B z : ℕ) :
    highestRaw A B z 0 = 1 / Real.sqrt (B.choose z : ℝ) := by
  simp [highestRaw]

theorem highestUnit_ne_zero (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p ≤ z) : highestUnit A B z p ≠ 0 :=
  div_ne_zero (highestRaw_ne_zero A B z p hA hB hp)
    (ne_of_gt (highestNorm_pos A B z hA hB))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Highest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem highestUnit_div_eq_raw (A B z p q : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    highestUnit A B z p / highestUnit A B z q =
      highestRaw A B z p / highestRaw A B z q := by
  unfold highestUnit
  exact div_div_div_cancel_right₀ (ne_of_gt (highestNorm_pos A B z hA hB)) _ _

theorem highest_end_ratio (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    highestUnit A B z z / highestUnit A B z 0 =
      (-1 : ℝ)^z * Real.sqrt ((B.choose z : ℝ)/(A.choose z : ℝ)) := by
  rw [highestUnit_div_eq_raw A B z z 0 hA hB,highestRaw_zero]
  simp only [highestRaw,le_refl,ite_true,Nat.choose_self,Nat.sub_self,
    Nat.choose_zero_right,Nat.cast_one,mul_one]
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,one_mul,inv_inv]
  ring

theorem highest_penultimate_ratio (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hz : 1 ≤ z) :
    highestUnit A B z (z-1) / highestUnit A B z 0 =
      (-1 : ℝ)^(z-1) * (z : ℝ) *
        Real.sqrt ((B.choose z : ℝ)/((A.choose (z-1) : ℝ)*B)) := by
  rw [highestUnit_div_eq_raw A B z (z-1) 0 hA hB,highestRaw_zero]
  simp only [highestRaw,ite_eq_left (show z-1 ≤ z by omega)]
  rw [show z-(z-1)=1 by omega,Nat.choose_one_right,
    Nat.choose_symm hz,Nat.choose_one_right]
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,one_mul,inv_inv]
  ring

theorem choose_ratio_descFactorial (A B z : ℕ) :
    (B.choose z : ℝ)/(A.choose z : ℝ) =
      (B.descFactorial z : ℝ)/(A.descFactorial z : ℝ) := by
  simp only [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  rw [mul_div_mul_left _ _ (by positivity : (z.factorial : ℝ) ≠ 0)]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_GramReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem source_readout_rational_identity (Q z : ℕ) (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hz₀ : 1 ≤ z) :
    (z : ℝ)^2*(Q.choose z : ℝ)/((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ)) +
      ((z : ℝ)-1)*(Q.choose z : ℝ)/((2*Q-2).choose z : ℝ) =
    (Q.choose z : ℝ)/((2*Q-2).choose z : ℝ)*
      (3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/Q) := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hc : (((2*Q-2).choose z : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega : z ≤ 2*Q-2))
  have hp : (((2*Q-2).choose (z-1) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega : z-1 ≤ 2*Q-2))
  have he := choose_step_real (2*Q-2) (z-1) (by omega)
  rw [show z-1+1=z by omega] at he
  have hcast : ((z-1 : ℕ) : ℝ)+1 = (z : ℝ) := by
    rw [Nat.cast_sub hz₀]; push_cast; ring
  have hcast' : ((2*Q-2-(z-1) : ℕ) : ℝ) = 2*(Q : ℝ)-1-z := by
    rw [Nat.cast_sub (by omega : z-1 ≤ 2*Q-2),Nat.cast_sub (by omega : 2 ≤ 2*Q),
      Nat.cast_sub hz₀]; push_cast; ring
  rw [hcast,hcast'] at he
  field_simp
  linear_combination (z : ℝ)*(Q.choose z : ℝ)*he

theorem highestReadout_eq_formula (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    highestReadout Q z = gramEigenvalueFormula Q z * highestUnit (2*Q-2) Q z 0 := by
  by_cases hz₀ : z = 0
  · subst z
    simp [highestReadout,gramEigenvalueFormula,fallingRatio]
  have hzpos : 1 ≤ z := by omega
  have hA : z ≤ 2*Q-2 := by omega
  have hs := highestUnit_ne_zero (2*Q-2) Q z 0 hA hz (by omega)
  have hend := highest_end_ratio (2*Q-2) Q z hA hz
  have hprev := highest_penultimate_ratio (2*Q-2) Q z hA hz hzpos
  have hsign : (-1 : ℝ)^z = -((-1 : ℝ)^(z-1)) := by
    have hh : z = (z-1)+1 := by omega
    conv_lhs => rw [hh,pow_succ]
    ring
  have hprev' := (div_eq_iff hs).mp hprev
  have hend' := (div_eq_iff hs).mp hend
  rw [highestReadout,ite_eq_right hz₀,hprev',hend']
  rw [show ((2*Q-2).choose (z-1) : ℝ)*(Q : ℝ) =
    (Q : ℝ)*((2*Q-2).choose (z-1) : ℝ) by ring]
  have he := source_readout_rational_identity Q z hQ hz hzpos
  have hc := choose_ratio_descFactorial (2*Q-2) Q z
  change (Q.choose z : ℝ)/((2*Q-2).choose z : ℝ) = fallingRatio Q z at hc
  calc
    _ = (-1 : ℝ)^z * ((z : ℝ)^2 * (Q.choose z : ℝ) /
        ((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ)) +
      ((z : ℝ)-1)*(Q.choose z : ℝ)/((2*Q-2).choose z : ℝ)) *
      highestUnit (2*Q-2) Q z 0 := by
      rw [hsign]
      have h₁ := Real.sq_sqrt (show 0 ≤ (Q.choose z : ℝ)/
        ((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ)) by positivity)
      have h₂ := Real.sq_sqrt (show 0 ≤ (Q.choose z : ℝ)/((2*Q-2).choose z : ℝ) by positivity)
      linear_combination
        -((-1 : ℝ)^(z-1))*(z : ℝ)^2*highestUnit (2*Q-2) Q z 0*h₁ +
        -((-1 : ℝ)^(z-1))*((z : ℝ)-1)*highestUnit (2*Q-2) Q z 0*h₂
    _ = _ := by rw [he,hc]; unfold gramEigenvalueFormula; ring

end Laughlin.Spin

end OAI
end

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

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_GramSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairCoefficient_base (Q : ℕ) (hQ : 2 ≤ Q) (x y : Fin (Q+1)) :
    pairCoefficient Q 0 x y =
      if x.val = 0 ∧ y.val = 1 then -(1/Real.sqrt 2) else
      if x.val = 1 ∧ y.val = 0 then 1/Real.sqrt 2 else 0 := by
  rw [pairCoefficient_choose Q 0 (by omega) (by omega)]
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hr : (Q : ℝ)/(2*Q) = 1/2 := by field_simp
  by_cases hs : x.val+y.val=1
  · have hc : (x.val=0 ∧ y.val=1) ∨ (x.val=1 ∧ y.val=0) := by omega
    rcases hc with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · simp [hx,hy,hr]
    · simp [hx,hy,hr]
  · have h₀ : ¬(x.val=0 ∧ y.val=1) := by omega
    have h₁ : ¬(x.val=1 ∧ y.val=0) := by omega
    rw [ite_eq_right hs,ite_eq_right h₀,ite_eq_right h₁]

theorem swap_base_row (Q q : ℕ) (hQ : 2 ≤ Q) (i j : Fin (Q+1)) :
    (∑ t : Fin (Q+1), pairCoefficient Q 0 j t * pairCoefficient Q q i t) =
      if j.val=0 then -pairCoefficient Q q i ⟨1,by omega⟩ / Real.sqrt 2 else
      if j.val=1 then pairCoefficient Q q i ⟨0,by omega⟩ / Real.sqrt 2 else 0 := by
  simp_rw [pairCoefficient_base Q hQ]
  have ht₀ (t : Fin (Q+1)) : t.val=0 ↔ t=(⟨0,Nat.zero_lt_succ Q⟩ : Fin (Q+1)) := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  have ht₁ (t : Fin (Q+1)) : t.val=1 ↔ t=(⟨1,Nat.lt_succ_of_le (le_trans (by decide : 1 ≤ 2) hQ)⟩ : Fin (Q+1)) := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  by_cases hj₀ : j.val=0
  · simp [hj₀,ht₁]; ring
  · by_cases hj₁ : j.val=1
    · simp [hj₁,ht₀]; ring
    · simp [hj₀,hj₁]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_HighestReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem threeBodyGram_highest_first_coordinate_s50_oai (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (∑ q : Fin (z+1), threeBodyGramSlice Q z hz ⟨0,by omega⟩ q *
      Spin.highestUnit (2*Q-2) Q z q.val) =
      (1+gramEigenvalueFormula Q z)*Spin.highestUnit (2*Q-2) Q z 0 := by
  by_cases hz₀ : z=0
  · subst z
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (1-2*∑ t : Fin (Q+1),
      pairCoefficient Q 0 ⟨0,Nat.zero_lt_succ Q⟩ t *
      pairCoefficient Q 0 ⟨0,Nat.zero_lt_succ Q⟩ t) *
      Spin.highestUnit (2*Q-2) Q 0 0 + 0 = _
    rw [swap_base_row Q 0 hQ]
    simp [pairCoefficient_base Q hQ,gramEigenvalueFormula,fallingRatio]
    left
    have hn : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  · rw [threeBodyGramSlice_first_row_pos_s50 Q z hQ hz (by omega)]
    have he := Spin.highestReadout_eq_formula Q z hQ hz
    unfold Spin.highestReadout at he
    rw [ite_eq_right hz₀] at he
    linear_combination he

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.threeBodyGram_highest_first_coordinate_s50_oai := @OAI.Laughlin.Fock.threeBodyGram_highest_first_coordinate_s50_oai
