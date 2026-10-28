-- Prove2me | solution 1 for OAI.Laughlin.Fock.complexThreeSpinProjector_eigen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:31:49.946003+00:00
-- url     : https://prove2.me/submissions/f12694eb-612d-40a5-8b15-0d40ce68cc6c

import Mathlib
import Definitions.Def_Laughlin
import Definitions.Def_OAIQ047L002
import Definitions.Def_OAIQ047L003
import Theorems.Thm_OAI_Laughlin_Spin_threeGram_on_slice

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Highest2
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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_HighestSpace
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

theorem highest_unique (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : ℕ → ℝ)
    (hf : ∀ p < z, ladder A p*f (p+1)+ladder B (z-p-1)*f p = 0) :
    ∀ p ≤ z, f p = (f 0 / highestRaw A B z 0)*highestRaw A B z p := by
  intro p hp
  induction p with
  | zero => field_simp [highestRaw_ne_zero A B z 0 hA hB (by omega)]
  | succ p ih =>
    have hlt : p < z := by omega
    have he := highestRaw_raising A B z p hA hB hlt
    have hh := hf p hlt
    have hi := ih (by omega)
    have ha : ladder A p ≠ 0 := ne_of_gt (ladder_pos A p (by omega))
    apply (mul_left_cancel₀ ha)
    linear_combination hh - (f 0 / highestRaw A B z 0)*he - ladder B (z-p-1)*hi

theorem highestUnit_ne_zero (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p ≤ z) : highestUnit A B z p ≠ 0 :=
  div_ne_zero (highestRaw_ne_zero A B z p hA hB hp)
    (ne_of_gt (highestNorm_pos A B z hA hB))

theorem raiseSlice_kernel (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) :
    (∀ p, raiseSlice A B z f p = 0) ↔
      ∃ c : ℝ, ∀ p, f p = c*highestUnit A B z p.val := by
  constructor
  · intro hf
    let g : ℕ → ℝ := fun p => if h : p < z+1 then f ⟨p,h⟩ else 0
    have hg : ∀ p < z, ladder A p*g (p+1)+ladder B (z-p-1)*g p = 0 := by
      intro p hp
      simpa [g,raiseSlice,hp,show p ≤ z by omega] using hf ⟨p,hp⟩
    refine ⟨(g 0 / highestRaw A B z 0)*highestNorm A B z,?_⟩
    intro p
    have he := highest_unique A B z hA hB g hg p.val (by omega)
    have hn := ne_of_gt (highestNorm_pos A B z hA hB)
    have hfval : g p.val = f p := by simp [g,show p.val ≤ z by omega]
    rw [hfval] at he
    rw [he]
    unfold highestUnit
    field_simp
  · rintro ⟨c,hc⟩ p
    simp only [raiseSlice,hc]
    linear_combination c * highestUnit_raising A B z p.val hA hB p.isLt

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Highest
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
-- module Solutions.OAIQ047_LA.Laughlin_Operators_GramReadout
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
-- module Solutions.OAIQ047_LA.Laughlin_Pair_Orthonormality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairCoefficient_swap (Q p : ℕ) (x y : Fin (Q+1)) :
    pairCoefficient Q p y x = -pairCoefficient Q p x y := by
  unfold pairCoefficient
  rw [Nat.add_comm y.val x.val]
  split_ifs
  · have hn : ((Q.descFactorial y.val : ℝ) * (Q.descFactorial x.val : ℝ) * (p.factorial : ℝ)) =
        ((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) * (p.factorial : ℝ)) := by ring
    have hd : ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (y.val.factorial : ℝ) * (x.val.factorial : ℝ)) =
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.val.factorial : ℝ) * (y.val.factorial : ℝ)) := by ring
    rw [hn, hd]
    ring
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_LoweringAlgebra
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
-- module Solutions.OAIQ047_LA.Laughlin_Pair_PolynomialBridge
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
-- module Solutions.OAIQ047_LA.Laughlin_Pair_PolynomialLadder
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
-- module Solutions.OAIQ047_LA.Laughlin_Pair_NormalizedLadder
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

theorem normalizedPairState_lowering (Q p i j : ℕ) (hQ : 0 < Q)
    (hp : p < 2*Q-2) (hi : i ≤ Q) (hj : j ≤ Q) :
    lowerPair Q (normalizedPairState Q p) i j =
      Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*normalizedPairState Q (p+1) i j := by
  unfold normalizedPairState
  rw [lowerPair_div, rawPairState_lowering Q p i j hi hj]
  push_cast
  calc
    _ = (((p : ℝ)+1)/pairNormalization Q p)*rawPairState Q (p+1) i j := by ring
    _ = _ := by rw [pairNormalization_ratio Q p hQ hp]; ring

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
-- module Solutions.OAIQ047_LA.Laughlin_Pair_PolynomialRaising
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
-- module Solutions.OAIQ047_LA.Laughlin_Pair_TensorLower
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

theorem pairTensorLower_weight (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
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

theorem pairCoefficient_tensor_lowering (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorLower Q p x y = ladder (2*Q-2) p * pairCoefficient Q (p+1) x y := by
  have hx : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have hy : Real.sqrt (Q.choose y.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : y.val ≤ Q)
  apply (mul_right_cancel₀ hy)
  apply (mul_right_cancel₀ hx)
  have he := pairTensorLower_weight Q p hQ (by omega) x y
  rw [normalizedPairState_lowering Q p x.val y.val hQ hp (by omega) (by omega),
    normalizedPairState_eq_coefficients Q (p+1) hQ (by omega) x y] at he
  unfold ladder
  linear_combination he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_TensorRaise
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

theorem pairCoefficient_tensor_raising (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
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

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_TensorBoundary
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

theorem pairCoefficient_tensor_lowest (Q : ℕ) (hQ : 0 < Q)
    (x y : Fin (Q+1)) : pairTensorLower Q (2*Q-2) x y = 0 := by
  have he := pairTensorLower_weight Q (2*Q-2) hQ (by omega) x y
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
-- module Solutions.OAIQ047_LA.Laughlin_Pair_LadderIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairInclusion_raising (Q : ℕ) (hQ : 0 < Q) :
    totalRaise Q Q * pairInclusion Q = pairInclusion Q * raiseMatrix (2*Q-2) := by
  ext i p
  change (∑ j, totalRaise Q Q i j*pairCoefficient Q p.val j.1 j.2) =
    ∑ k, pairCoefficient Q k.val i.1 i.2 * raiseMatrix (2*Q-2) k p
  rw [totalRaise_apply,raiseMatrix_row,raiseMatrix_row,raiseMatrix_column]
  change pairTensorRaise Q p.val i.1 i.2 = _
  by_cases hp : 0 < p.val
  · rw [dite_eq_left hp]
    have he := pairCoefficient_tensor_raising Q (p.val-1) hQ (by omega) i.1 i.2
    rw [show p.val-1+1=p.val by omega] at he
    simpa only [mul_comm] using he
  · rw [dite_eq_right hp]
    have hz : p.val=0 := by omega
    rw [hz,pairCoefficient_tensor_highest Q hQ]

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
  · rw [dite_eq_left hp,pairCoefficient_tensor_lowering Q p.val hQ hp]
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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_TripleLadderIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem tripleInclusion_raising (Q : ℕ) (hQ : 0 < Q) :
    tripleRaise Q * tripleInclusion Q = tripleInclusion Q * totalRaise (2*Q-2) Q := by
  rw [totalRaise_kronecker]
  unfold tripleRaise tripleInclusion
  simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_kronecker_mul,
    Matrix.mul_one,Matrix.one_mul,pairInclusion_raising Q hQ]

theorem tripleInclusion_transpose (Q : ℕ) :
    (tripleInclusion Q)ᵀ = (pairInclusion Q)ᵀ ⊗ₖ (1 : Matrix (Orbital Q) (Orbital Q) ℝ) := by
  ext i j
  simp [tripleInclusion,Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]

theorem tripleInclusion_transpose_raising (Q : ℕ) (hQ : 0 < Q) :
    (tripleInclusion Q)ᵀ * tripleRaise Q = totalRaise (2*Q-2) Q * (tripleInclusion Q)ᵀ := by
  rw [tripleInclusion_transpose,totalRaise_kronecker]
  unfold tripleRaise
  simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_kronecker_mul,
    Matrix.mul_one,Matrix.one_mul,pairInclusion_transpose_raising Q hQ]

theorem swap23Matrix_mul (Q : ℕ) (M : Matrix (TripleIndex Q) (TripleIndex Q) ℝ)
    (i j : TripleIndex Q) : (swap23Matrix Q * M) i j = M (swap23 i) j := by
  simp [Matrix.mul_apply,swap23Matrix]

theorem mul_swap23Matrix (Q : ℕ) (M : Matrix (TripleIndex Q) (TripleIndex Q) ℝ)
    (i j : TripleIndex Q) : (M * swap23Matrix Q) i j = M i (swap23 j) := by
  have he (k : TripleIndex Q) : swap23 k=j ↔ k=swap23 j := by
    constructor
    · intro h; simpa using congrArg swap23 h
    · intro h; rw [h,swap23_involutive]
  simp [Matrix.mul_apply,swap23Matrix,he]

theorem swap23_raising (Q : ℕ) : swap23Matrix Q * tripleRaise Q = tripleRaise Q * swap23Matrix Q := by
  ext a b
  rw [swap23Matrix_mul,mul_swap23Matrix]
  rcases a with ⟨⟨i,j⟩,k⟩
  rcases b with ⟨⟨l,m⟩,n⟩
  simp only [tripleRaise,totalRaise,Matrix.add_apply,Matrix.kroneckerMap,
    Matrix.one_apply,Matrix.of_apply,swap23,Prod.mk.injEq]
  split_ifs <;> simp_all
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_GramSlice
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
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_HighestRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairCoefficient_endpoint_zero (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hz₀ : 1 ≤ z) :
    pairCoefficient Q (z-1) ⟨z,by omega⟩ ⟨0,by omega⟩ =
      (z : ℝ)/Real.sqrt 2 * Real.sqrt ((Q.choose z : ℝ)/
        ((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ))) := by
  rw [pairCoefficient_choose Q (z-1) (by omega) (by omega)]
  rw [ite_eq_left (show z+0=z-1+1 by omega)]
  simp only [Nat.cast_zero,sub_zero,
    Nat.choose_zero_right,Nat.cast_one,mul_one]
  rw [show (Q.choose z : ℝ)/(2*(Q : ℝ)*((2*Q-2).choose (z-1) : ℝ)) =
    ((Q.choose z : ℝ)/((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ)))/2 by ring]
  rw [Real.sqrt_div (by positivity)]
  ring

theorem pairCoefficient_endpoint_one (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    pairCoefficient Q z ⟨z,by omega⟩ ⟨1,by omega⟩ =
      ((z : ℝ)-1)/Real.sqrt 2 *
        Real.sqrt ((Q.choose z : ℝ)/((2*Q-2).choose z : ℝ)) := by
  rw [pairCoefficient_choose Q z (by omega) (by omega)]
  simp only [ite_true,Nat.choose_one_right,Nat.cast_one]
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hr : (Q.choose z : ℝ)*Q/(2*(Q : ℝ)*((2*Q-2).choose z : ℝ)) =
      ((Q.choose z : ℝ)/((2*Q-2).choose z : ℝ))/2 := by field_simp
  rw [hr,Real.sqrt_div (by positivity)]
  ring

theorem swap_slice_first_row (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hz₀ : 1 ≤ z) (f : Fin (z+1) → ℝ) :
    (∑ q : Fin (z+1), (∑ t : Fin (Q+1),
      pairCoefficient Q 0 (sliceOrbital Q z hz q) t *
        pairCoefficient Q q.val ⟨z,by omega⟩ t)*f q) =
      (-pairCoefficient Q z ⟨z,by omega⟩ ⟨1,by omega⟩ /Real.sqrt 2)*f ⟨z,by omega⟩ +
      (pairCoefficient Q (z-1) ⟨z,by omega⟩ ⟨0,by omega⟩ /Real.sqrt 2)*f ⟨z-1,by omega⟩ := by
  let last : Fin (z+1) := ⟨z,by omega⟩
  let prev : Fin (z+1) := ⟨z-1,by omega⟩
  have hne : last ≠ prev := by intro h; have := congrArg Fin.val h; dsimp [last,prev] at this; omega
  have he (q : Fin (z+1)) :
      (∑ t : Fin (Q+1), pairCoefficient Q 0 (sliceOrbital Q z hz q) t *
        pairCoefficient Q q.val ⟨z,by omega⟩ t) =
        (if q=last then -pairCoefficient Q z ⟨z,by omega⟩ ⟨1,by omega⟩ /Real.sqrt 2 else 0) +
        (if q=prev then pairCoefficient Q (z-1) ⟨z,by omega⟩ ⟨0,by omega⟩ /Real.sqrt 2 else 0) := by
    rw [swap_base_row Q q.val hQ]
    by_cases hl : q=last
    · subst q
      simp [last,prev,sliceOrbital,show z ≠ z-1 by omega]
    · by_cases hp : q=prev
      · subst q
        simp [last,prev,sliceOrbital,show z-(z-1)=1 by omega,show z-1 ≠ z by omega]
      · have hlv : q.val ≠ z := by intro h; apply hl; exact Fin.ext h
        have hpv : q.val ≠ z-1 := by intro h; apply hp; exact Fin.ext h
        have hzero : z-q.val ≠ 0 := by omega
        have hone : z-q.val ≠ 1 := by omega
        simp [hl,hp,sliceOrbital,hzero,hone]
  simp_rw [he,add_mul,ite_mul,zero_mul]
  rw [Finset.sum_add_distrib]
  simp [last,prev]

theorem threeBodyGramSlice_first_row_pos (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hz₀ : 1 ≤ z) (f : Fin (z+1) → ℝ) :
    (∑ q : Fin (z+1), threeBodyGramSlice Q z hz ⟨0,by omega⟩ q*f q) =
      f ⟨0,by omega⟩ - f ⟨z-1,by omega⟩ * (z : ℝ) *
        Real.sqrt ((Q.choose z : ℝ)/((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ))) +
      f ⟨z,by omega⟩*((z : ℝ)-1)*
        Real.sqrt ((Q.choose z : ℝ)/((2*Q-2).choose z : ℝ)) := by
  simp only [threeBodyGramSlice,sub_mul,mul_assoc]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  have horb : sliceOrbital Q z hz ⟨0,by omega⟩ = ⟨z,by omega⟩ := by rfl
  rw [horb,swap_slice_first_row Q z hQ hz hz₀ f]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [pairCoefficient_endpoint_zero Q z hQ hz hz₀,pairCoefficient_endpoint_one Q z hQ hz]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  field_simp
  rw [hsq]
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_HighestReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem threeBodyGram_highest_first_coordinate (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
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
  · rw [threeBodyGramSlice_first_row_pos Q z hQ hz (by omega)]
    have he := Spin.highestReadout_eq_formula Q z hQ hz
    unfold Spin.highestReadout at he
    rw [ite_eq_right hz₀] at he
    linear_combination he

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_SpinCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem swapCompression_raising (Q : ℕ) (hQ : 0 < Q) :
    swapCompression Q * totalRaise (2*Q-2) Q = totalRaise (2*Q-2) Q * swapCompression Q := by
  unfold swapCompression
  calc
    _ = (tripleInclusion Q)ᵀ * swap23Matrix Q *
      (tripleInclusion Q * totalRaise (2*Q-2) Q) := by simp only [Matrix.mul_assoc]
    _ = (tripleInclusion Q)ᵀ * swap23Matrix Q *
      (tripleRaise Q * tripleInclusion Q) := by rw [tripleInclusion_raising Q hQ]
    _ = (tripleInclusion Q)ᵀ * (swap23Matrix Q * tripleRaise Q) * tripleInclusion Q := by
      simp only [Matrix.mul_assoc]
    _ = (tripleInclusion Q)ᵀ * (tripleRaise Q * swap23Matrix Q) * tripleInclusion Q := by
      rw [swap23_raising]
    _ = ((tripleInclusion Q)ᵀ * tripleRaise Q) * swap23Matrix Q * tripleInclusion Q := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [tripleInclusion_transpose_raising Q hQ]; simp only [Matrix.mul_assoc]

theorem threeGram_raising (Q : ℕ) (hQ : 0 < Q) :
    threeGram Q * totalRaise (2*Q-2) Q = totalRaise (2*Q-2) Q * threeGram Q := by
  simp only [threeGram,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
    Matrix.smul_mul,Matrix.mul_smul,swapCompression_raising Q hQ]

theorem swapCompression_entry (Q : ℕ) (a b : PairOrbitalIndex Q) :
    swapCompression Q a b = ∑ t : Orbital Q,
      pairCoefficient Q a.1.val b.2 t * pairCoefficient Q b.1.val a.2 t := by
  have he (i : TripleIndex Q) :
      ((tripleInclusion Q)ᵀ * swap23Matrix Q) a i = tripleInclusion Q (swap23 i) a := by
    have hi (k : TripleIndex Q) : swap23 k=i ↔ k=swap23 i := by
      constructor
      · intro h; simpa using congrArg swap23 h
      · intro h; rw [h,swap23_involutive]
    simp [Matrix.mul_apply,swap23Matrix,hi,Matrix.transpose_apply]
  unfold swapCompression
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [tripleInclusion,pairInclusion,Matrix.kroneckerMap,
    Matrix.of_apply,Matrix.one_apply,swap23]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro t ht
  rw [pairCoefficient_swap Q a.1.val t b.2,pairCoefficient_swap Q b.1.val t a.2]
  ring

theorem threeGram_entry (Q : ℕ) (a b : PairOrbitalIndex Q) :
    threeGram Q a b = (if a=b then 1 else 0) - 2*∑ t : Orbital Q,
      pairCoefficient Q a.1.val b.2 t * pairCoefficient Q b.1.val a.2 t := by
  simp only [threeGram,Matrix.sub_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,
    swapCompression_entry]

theorem threeGram_weight (Q : ℕ) (a b : PairOrbitalIndex Q)
    (h : a.1.val+a.2.val ≠ b.1.val+b.2.val) : threeGram Q a b = 0 := by
  have hab : a ≠ b := by intro he; apply h; rw [he]
  rw [threeGram_entry,ite_eq_right hab]
  have hz : (∑ t : Orbital Q, pairCoefficient Q a.1.val b.2 t *
      pairCoefficient Q b.1.val a.2 t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    by_cases ha : b.2.val+t.val=a.1.val+1
    · have hb : a.2.val+t.val ≠ b.1.val+1 := by omega
      simp [pairCoefficient,hb]
    · simp [pairCoefficient,ha]
  rw [hz]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_HighestEigen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem threeGram_extend_off (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (f : Fin (z+1) → ℝ) (i : PairOrbitalIndex Q) (hi : i.1.val+i.2.val ≠ z) :
    (threeGram Q *ᵥ extendWeightSlice (2*Q-2) Q z (by omega) hz f) i = 0 := by
  change (∑ j, threeGram Q i j * extendWeightSlice (2*Q-2) Q z (by omega) hz f j) = 0
  rw [sum_extendWeightSlice]
  apply Finset.sum_eq_zero
  intro p hp
  rw [threeGram_weight]
  · ring
  · dsimp [weightSliceIndex]
    omega

theorem threeGram_highest_eigen (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeGram Q *ᵥ coupledHighest Q z hQ hz =
      (1+gramEigenvalueFormula Q z) • coupledHighest Q z hQ hz := by
  let v := coupledHighest Q z hQ hz
  let g := threeGram Q *ᵥ v
  let f : Fin (z+1) → ℝ := fun p => g (weightSliceIndex (2*Q-2) Q z (by omega) hz p)
  have hv : totalRaise (2*Q-2) Q *ᵥ v = 0 := by
    apply extendWeightSlice_highest
    intro p
    exact highestUnit_raising (2*Q-2) Q z p.val (by omega) hz p.isLt
  have hg : totalRaise (2*Q-2) Q *ᵥ g = 0 := by
    dsimp [g]
    rw [Matrix.mulVec_mulVec,← threeGram_raising Q (by omega),← Matrix.mulVec_mulVec,hv,
      Matrix.mulVec_zero]
  have hf : ∀ p, raiseSlice (2*Q-2) Q z f p = 0 := by
    intro p
    have he := congrFun hg ((⟨p.val,by omega⟩,⟨z-p.val-1,by omega⟩) : PairOrbitalIndex Q)
    rw [totalRaise_below_slice (2*Q-2) Q z (by omega) hz] at he
    exact he
  obtain ⟨c,hc⟩ := (raiseSlice_kernel (2*Q-2) Q z (by omega) hz f).mp hf
  have hfirst : f ⟨0,by omega⟩ =
      (1+gramEigenvalueFormula Q z)*highestUnit (2*Q-2) Q z 0 := by
    dsimp [f,g,v,coupledHighest]
    change (∑ j,threeGram Q _ j*extendWeightSlice (2*Q-2) Q z (by omega) hz _ j) = _
    rw [sum_extendWeightSlice]
    simp_rw [threeGram_on_slice Q z hQ hz]
    exact Fock.threeBodyGram_highest_first_coordinate Q z hQ hz
  have hcz : c = 1+gramEigenvalueFormula Q z := by
    apply (mul_right_cancel₀ (highestUnit_ne_zero (2*Q-2) Q z 0 (by omega) hz (by omega)))
    exact (hc ⟨0,by omega⟩).symm.trans hfirst
  funext i
  change g i = (1+gramEigenvalueFormula Q z)*v i
  by_cases hi : i.1.val+i.2.val=z
  · let p : Fin (z+1) := ⟨i.1.val,by omega⟩
    have he : i = weightSliceIndex (2*Q-2) Q z (by omega) hz p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    rw [he]
    change f p = (1+gramEigenvalueFormula Q z)*extendWeightSlice (2*Q-2) Q z (by omega) hz _ _
    rw [extendWeightSlice_at,hc p,hcz]
  · have hg₀ : g i = 0 := threeGram_extend_off Q z hQ hz _ i hi
    have hv₀ : v i = 0 := extendWeightSlice_off (2*Q-2) Q z (by omega) hz _ i hi
    rw [hg₀,hv₀,mul_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_Descendants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem threeGram_transpose (Q : ℕ) : (threeGram Q)ᵀ = threeGram Q := by
  ext a b
  simp only [Matrix.transpose_apply,threeGram_entry]
  have hd : (if b=a then (1 : ℝ) else 0) = (if a=b then 1 else 0) := by
    by_cases h : a=b
    · simp [h]
    · simp [h,Ne.symm h]
  rw [hd]
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem threeGram_lowering (Q : ℕ) (hQ : 0 < Q) :
    threeGram Q * (totalRaise (2*Q-2) Q)ᵀ = (totalRaise (2*Q-2) Q)ᵀ * threeGram Q := by
  have h := congrArg Matrix.transpose (threeGram_raising Q hQ)
  simpa only [Matrix.transpose_mul,threeGram_transpose] using h.symm

theorem coupledDescendant_succ (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    coupledDescendant Q z hQ hz (n+1) =
      (totalRaise (2*Q-2) Q)ᵀ *ᵥ coupledDescendant Q z hQ hz n := by
  simp only [coupledDescendant,pow_succ',Matrix.mulVec_mulVec]

theorem threeGram_descendant_eigen (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    threeGram Q *ᵥ coupledDescendant Q z hQ hz n =
      (1+gramEigenvalueFormula Q z) • coupledDescendant Q z hQ hz n := by
  induction n with
  | zero => simpa [coupledDescendant] using threeGram_highest_eigen Q z hQ hz
  | succ n ih =>
    rw [coupledDescendant_succ,Matrix.mulVec_mulVec,threeGram_lowering Q (by omega),
      ← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul]

theorem threeGram_sub_one_descendant_eigen (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    (threeGram Q-1) *ᵥ coupledDescendant Q z hQ hz n =
      gramEigenvalueFormula Q z • coupledDescendant Q z hQ hz n := by
  rw [Matrix.sub_mulVec,threeGram_descendant_eigen,Matrix.one_mulVec]
  funext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_DescendantNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem normalizedCoupledDescendant_eigen (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (threeGram Q-1) *ᵥ normalizedCoupledDescendant Q z hQ hz n =
      gramEigenvalueFormula Q z • normalizedCoupledDescendant Q z hQ hz n := by
  unfold normalizedCoupledDescendant
  rw [Matrix.mulVec_smul,threeGram_sub_one_descendant_eigen,smul_comm]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledBasis_eigen (Q : ℕ) (hQ : 2 ≤ Q) :
    (threeGram Q-1)*coupledBasisMatrix Q hQ =
      coupledBasisMatrix Q hQ * Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val) := by
  ext i s
  rw [Matrix.mul_apply,Matrix.mul_diagonal]
  have he := congrFun (normalizedCoupledDescendant_eigen Q s.1.val s.2.val hQ (by omega)) i
  simpa only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,coupledBasisMatrix,mul_comm] using he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_SpinProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledSelector_eigen (Q : ℕ) (z : Fin (Q+1)) :
    Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val) *
      coupledSelector Q z = gramEigenvalueFormula Q z.val • coupledSelector Q z := by
  unfold coupledSelector
  rw [Matrix.diagonal_mul_diagonal]
  ext s t
  by_cases hst : s=t
  · subst t
    simp only [Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul]
    by_cases h : s.1=z
    · simp [h]
    · simp [h]
  · simp [hst]

theorem threeSpinProjector_sub_one_eigen (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    (threeGram Q-1)*threeSpinProjector Q hQ z =
      gramEigenvalueFormula Q z.val • threeSpinProjector Q hQ z := by
  unfold threeSpinProjector
  calc
    _ = ((threeGram Q-1)*coupledBasisMatrix Q hQ)*coupledSelector Q z*(coupledBasisMatrix Q hQ)ᵀ := by
      simp only [Matrix.mul_assoc]
    _ = coupledBasisMatrix Q hQ *
      (Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val)*coupledSelector Q z)*
      (coupledBasisMatrix Q hQ)ᵀ := by rw [coupledBasis_eigen]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [coupledSelector_eigen]; simp only [Matrix.mul_smul,Matrix.smul_mul]

theorem threeSpinProjector_eigen (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    threeGram Q*threeSpinProjector Q hQ z =
      (1+gramEigenvalueFormula Q z.val) • threeSpinProjector Q hQ z := by
  have he := threeSpinProjector_sub_one_eigen Q hQ z
  rw [Matrix.sub_mul,Matrix.one_mul] at he
  calc
    _ = (threeGram Q*threeSpinProjector Q hQ z-threeSpinProjector Q hQ z)+threeSpinProjector Q hQ z := by abel
    _ = gramEigenvalueFormula Q z.val • threeSpinProjector Q hQ z+threeSpinProjector Q hQ z := by rw [he]
    _ = _ := by ext i j; simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_NullSectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem complexThreeSpinProjector_eigen_oai (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    complexThreeGram Q * complexThreeSpinProjector Q hQ z =
      ((1+gramEigenvalueFormula Q z.val : ℝ) : ℂ) • complexThreeSpinProjector Q hQ z := by
  ext a b
  have he := congrArg (fun M : Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℝ =>
    (M a b : ℂ)) (Spin.threeSpinProjector_eigen Q hQ z)
  simp only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul] at he ⊢
  push_cast at he
  simpa only [complexThreeGram,complexThreeSpinProjector,Complex.ofReal_add,Complex.ofReal_one] using he

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.complexThreeSpinProjector_eigen_oai := @OAI.Laughlin.Fock.complexThreeSpinProjector_eigen_oai
