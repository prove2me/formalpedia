-- Prove2me | solution 1 for OAI.Laughlin.Fock.threeBodyGramSlice_first_row_pos_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:01:11.910426+00:00
-- url     : https://prove2.me/submissions/845fe263-68a6-4127-9852-8691543c8577

import Mathlib
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L013

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_HighestRow
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

theorem threeBodyGramSlice_first_row_pos_s50_oai (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
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

theorem solution : type_of% @OAI.Laughlin.Fock.threeBodyGramSlice_first_row_pos_s50_oai := @OAI.Laughlin.Fock.threeBodyGramSlice_first_row_pos_s50_oai
