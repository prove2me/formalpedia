-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_threeBody_physical_traces_strict_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:39:38.163574+00:00
-- url     : https://prove2.me/submissions/37bd0740-d9fa-4840-ac3e-472d449cb7ea

import Mathlib
import Definitions.Def_OAIQ047L002
import Definitions.Def_OAIQ047L003

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

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_RelativeHighest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem highestRaw_zero_pos (A B z : ℕ) (hB : z ≤ B) :
    0 < highestRaw A B z 0 := by
  rw [highestRaw_zero]
  apply one_div_pos.mpr
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.choose_pos hB

theorem relativeHighest_zero (A B z : ℕ) (hB : z ≤ B) :
    relativeHighest A B z 0 = 1 := by
  exact div_self (ne_of_gt (highestRaw_zero_pos A B z hB))

theorem relativeHighest_succ (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p < z) :
    relativeHighest A B z (p+1) =
      -(ladder B (z-p-1)/ladder A p)*relativeHighest A B z p := by
  have he := highestRaw_raising A B z p hA hB hp
  have ha := ne_of_gt (ladder_pos A p (by omega))
  have hr := ne_of_gt (highestRaw_zero_pos A B z hB)
  unfold relativeHighest
  field_simp
  nlinarith only [he]

theorem highestNorm_relative (A B z : ℕ) (hB : z ≤ B) :
    highestNorm A B z = highestRaw A B z 0 * relativeHighestNorm A B z := by
  have hp := highestRaw_zero_pos A B z hB
  have he : (∑ p ∈ Finset.range (z+1), (highestRaw A B z p)^2) =
      (highestRaw A B z 0)^2 * ∑ p ∈ Finset.range (z+1), (relativeHighest A B z p)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp'
    unfold relativeHighest
    field_simp
  unfold highestNorm relativeHighestNorm
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (le_of_lt hp)]

theorem highestUnit_eq_relative (A B z p : ℕ) (hB : z ≤ B) :
    highestUnit A B z p = relativeHighest A B z p / relativeHighestNorm A B z := by
  unfold highestUnit relativeHighest
  rw [highestNorm_relative A B z hB]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_OscillatorHighest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem oscillatorRelative_zero (t : ℝ) (z : ℕ) :
    oscillatorRelative t z 0 = 1 := by simp [oscillatorRelative]

theorem sqrt_choose_ratio (z p : ℕ) (hp : p < z) :
    Real.sqrt (z.choose (p+1) : ℝ) =
      Real.sqrt ((z-p : ℕ)/(p+1 : ℝ)) * Real.sqrt (z.choose p : ℝ) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have he := choose_step_real z p (by omega)
  apply (mul_left_cancel₀ (show (p+1 : ℝ) ≠ 0 by positivity))
  field_simp
  nlinarith only [he]

theorem oscillatorRelative_succ (b : ℝ) (hb : 0 ≤ b) (z p : ℕ) (hp : p < z) :
    oscillatorRelative (Real.sqrt (b/(1-b))) z (p+1) =
      -Real.sqrt ((((z-p : ℕ) : ℝ)*b)/(((p : ℝ)+1)*(1-b))) *
        oscillatorRelative (Real.sqrt (b/(1-b))) z p := by
  have he : (((z-p : ℕ) : ℝ)*b)/(((p : ℝ)+1)*(1-b)) =
      ((z-p : ℕ)/(p+1 : ℝ))*(b/(1-b)) := by rw [mul_div_mul_comm]
  rw [he,Real.sqrt_mul (by positivity),Real.sqrt_div hb]
  unfold oscillatorRelative
  rw [sqrt_choose_ratio z p hp,pow_succ,pow_succ]
  ring

theorem oscillatorHighest_norm (u v : ℝ) (huv : u^2+v^2=1) (z : ℕ) :
    (∑ p ∈ Finset.range (z+1), (oscillatorHighest u v z p)^2) = 1 := by
  have hs := add_pow (u^2) (v^2) z
  rw [huv,one_pow] at hs
  apply Eq.trans ?_ hs.symm
  apply Finset.sum_congr rfl
  intro p hp
  unfold oscillatorHighest
  rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
  have hn : ((-1 : ℝ)^(z-p))^2 = 1 := by rw [← pow_mul,mul_comm _ 2,pow_mul]; norm_num
  rw [hn,one_mul]
  ring

theorem oscillatorHighest_relative (u v : ℝ) (hv : v ≠ 0) (z p : ℕ) (hp : p ≤ z) :
    (-1 : ℝ)^z * oscillatorRelative (u/v) z p * v^z = oscillatorHighest u v z p := by
  have hz : z=p+(z-p) := by omega
  have hsign : (-1 : ℝ)^z*(-1 : ℝ)^p = (-1 : ℝ)^(z-p) := by
    conv_lhs => arg 1; rw [hz,pow_add]
    have he : ((-1 : ℝ)^p)^2 = 1 := by rw [← pow_mul,mul_comm _ 2,pow_mul]; norm_num
    calc
      _ = ((-1 : ℝ)^p)^2 * (-1 : ℝ)^(z-p) := by ring
      _ = _ := by rw [he,one_mul]
  unfold oscillatorRelative oscillatorHighest
  calc
    _ = ((-1 : ℝ)^z*(-1 : ℝ)^p)*Real.sqrt (z.choose p : ℝ)*u^p*(v^z/v^p) := by rw [div_pow]; ring
    _ = _ := by
      have hpows : v^z = v^p*v^(z-p) := by rw [← pow_add,← hz]
      rw [hsign,hpows]; field_simp

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_OscillatorHighestNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem oscillatorRelativeNorm_pos (t : ℝ) (z : ℕ) : 0 < oscillatorRelativeNorm t z := by
  apply Real.sqrt_pos.mpr
  apply Finset.sum_pos'
  · intro p hp; exact sq_nonneg _
  · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
    rw [oscillatorRelative_zero]; norm_num

theorem oscillatorRelativeNorm_scale (u v : ℝ) (hv : 0 < v) (huv : u^2+v^2=1) (z : ℕ) :
    v^z * oscillatorRelativeNorm (u/v) z = 1 := by
  have hvz : 0 < v^z := pow_pos hv z
  have he : (v^z)^2 * ∑ p ∈ Finset.range (z+1), (oscillatorRelative (u/v) z p)^2 = 1 := by
    rw [Finset.mul_sum,← oscillatorHighest_norm u v huv z]
    apply Finset.sum_congr rfl
    intro p hp
    have hh := congrArg (fun x : ℝ => x^2)
      (oscillatorHighest_relative u v (ne_of_gt hv) z p (by have := Finset.mem_range.mp hp; omega))
    have hsign : ((-1 : ℝ)^z)^2 = 1 := by rw [← pow_mul,mul_comm _ 2,pow_mul]; norm_num
    simp only [mul_pow,hsign,one_mul] at hh
    nlinarith only [hh]
  have hs : (oscillatorRelativeNorm (u/v) z)^2 =
      ∑ p ∈ Finset.range (z+1), (oscillatorRelative (u/v) z p)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hn := oscillatorRelativeNorm_pos (u/v) z
  have hproduct : 0 < v^z*oscillatorRelativeNorm (u/v) z := mul_pos hvz hn
  rw [← hs] at he
  nlinarith only [he,hproduct]

theorem oscillatorHighest_from_relative (u v : ℝ) (hv : 0 < v) (huv : u^2+v^2=1)
    (z p : ℕ) (hp : p ≤ z) :
    (-1 : ℝ)^z * (oscillatorRelative (u/v) z p / oscillatorRelativeNorm (u/v) z) =
      oscillatorHighest u v z p := by
  have hs := oscillatorRelativeNorm_scale u v hv huv z
  have hn := ne_of_gt (oscillatorRelativeNorm_pos (u/v) z)
  have he := oscillatorHighest_relative u v (ne_of_gt hv) z p hp
  have hvz : v^z = 1 / oscillatorRelativeNorm (u/v) z := (eq_div_iff hn).mpr hs
  calc
    _ = (-1 : ℝ)^z * oscillatorRelative (u/v) z p * v^z := by rw [hvz]; ring
    _ = _ := he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_ScaleLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem spin_fraction_sub_tendsto (B S : ℕ → ℕ) (b : ℝ)
    (hB : Tendsto B atTop atTop) (hS : Tendsto S atTop atTop)
    (hfrac : Tendsto (fun n => (B n : ℝ)/(S n : ℝ)) atTop (𝓝 b)) (k : ℕ) :
    Tendsto (fun n => ((B n-k : ℕ) : ℝ)/(S n : ℝ)) atTop (𝓝 b) := by
  have hi := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hS
  have ht := hfrac.sub (hi.const_mul (k : ℝ))
  have he : (fun n => (B n : ℝ)/(S n : ℝ)-(k : ℝ)*(S n : ℝ)⁻¹) =ᶠ[atTop]
      (fun n => ((B n-k : ℕ) : ℝ)/(S n : ℝ)) := by
    filter_upwards [hB.eventually (eventually_ge_atTop k)] with n hn
    rw [Nat.cast_sub hn]
    ring
  simpa using ht.congr' he

theorem first_spin_fraction_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b)) :
    Tendsto (fun n => (A n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 (1-b)) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hfrac
  apply ht.congr'
  filter_upwards [hA.eventually (eventually_ge_atTop 1)] with n hn
  have hp : (0 : ℝ) < (A n : ℝ)+B n := by
    have h : (0 : ℝ) < A n := by exact_mod_cast (show 0 < A n by omega)
    positivity
  field_simp
  ring

theorem ladder_ratio_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb : b < 1)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b))
    (p k : ℕ) :
    Tendsto (fun n => ladder (B n) k / ladder (A n) p) atTop
      (𝓝 (Real.sqrt ((((k : ℝ)+1)*b)/(((p : ℝ)+1)*(1-b))))) := by
  have hS : Tendsto (fun n => A n+B n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right (A n) (B n)) hA
  have hb' : Tendsto (fun n => ((B n-k : ℕ) : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b) := by
    simpa only [Nat.cast_add] using spin_fraction_sub_tendsto B (fun n => A n+B n) b hB hS
      (by simpa only [Nat.cast_add] using hfrac) k
  have ha' : Tendsto (fun n => ((A n-p : ℕ) : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 (1-b)) := by
    simpa only [Nat.cast_add] using spin_fraction_sub_tendsto A (fun n => A n+B n) (1-b) hA hS
      (by simpa only [Nat.cast_add] using first_spin_fraction_tendsto A B b hA hfrac) p
  have hnz : ((p : ℝ)+1)*(1-b) ≠ 0 := by positivity
  have ht := ((hb'.const_mul ((k : ℝ)+1)).div (ha'.const_mul ((p : ℝ)+1)) hnz).sqrt
  apply ht.congr'
  filter_upwards [hA.eventually (eventually_ge_atTop 1)] with n hn
  have hp : (0 : ℝ) < (A n : ℝ)+B n := by
    have h : (0 : ℝ) < A n := by exact_mod_cast (show 0 < A n by omega)
    positivity
  have he : (((k : ℝ)+1)*(((B n-k : ℕ) : ℝ)/((A n : ℝ)+B n))) /
      (((p : ℝ)+1)*(((A n-p : ℕ) : ℝ)/((A n : ℝ)+B n))) =
      (((k : ℝ)+1)*((B n-k : ℕ) : ℝ))/(((p : ℝ)+1)*((A n-p : ℕ) : ℝ)) := by
    field_simp
  simp only [Pi.div_apply]
  rw [he,Real.sqrt_div (by positivity)]
  rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_HighestCouplingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

theorem relativeHighest_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b))
    (z p : ℕ) (hp : p ≤ z) :
    Tendsto (fun n => relativeHighest (A n) (B n) z p) atTop
      (𝓝 (oscillatorRelative (Real.sqrt (b/(1-b))) z p)) := by
  induction p with
  | zero =>
    rw [oscillatorRelative_zero]
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [hB.eventually (eventually_ge_atTop z)] with n hn
    exact (relativeHighest_zero (A n) (B n) z hn).symm
  | succ p ih =>
    have hlt : p < z := by omega
    have hr := ladder_ratio_tendsto A B b hA hB hb1 hfrac p (z-p-1)
    have hk : ((z-p-1 : ℕ) : ℝ)+1 = (z-p : ℕ) := by
      exact_mod_cast (show z-p-1+1=z-p by omega)
    rw [hk] at hr
    have ht := hr.neg.mul (ih (by omega))
    rw [oscillatorRelative_succ b (le_of_lt hb0) z p hlt]
    apply ht.congr'
    filter_upwards [hA.eventually (eventually_ge_atTop z),hB.eventually (eventually_ge_atTop z)] with n hnA hnB
    exact (relativeHighest_succ (A n) (B n) z p hnA hnB hlt).symm

theorem relativeHighestNorm_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b)) (z : ℕ) :
    Tendsto (fun n => relativeHighestNorm (A n) (B n) z) atTop
      (𝓝 (oscillatorRelativeNorm (Real.sqrt (b/(1-b))) z)) := by
  apply Tendsto.sqrt
  apply tendsto_finsetSum
  intro p hp
  exact (relativeHighest_tendsto A B b hA hB hb0 hb1 hfrac z p
    (by have := Finset.mem_range.mp hp; omega)).pow 2

theorem source_highest_coupling_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b))
    (z p : ℕ) (hp : p ≤ z) :
    Tendsto (fun n => (-1 : ℝ)^z * highestUnit (A n) (B n) z p) atTop
      (𝓝 (oscillatorHighest (Real.sqrt b) (Real.sqrt (1-b)) z p)) := by
  have huvs : (Real.sqrt b)^2+(Real.sqrt (1-b))^2=1 := by
    rw [Real.sq_sqrt (le_of_lt hb0),Real.sq_sqrt (by linarith)]; ring
  have hv : 0 < Real.sqrt (1-b) := Real.sqrt_pos.mpr (by linarith)
  have ht := ((relativeHighest_tendsto A B b hA hB hb0 hb1 hfrac z p hp).div
    (relativeHighestNorm_tendsto A B b hA hB hb0 hb1 hfrac z)
    (ne_of_gt (oscillatorRelativeNorm_pos (Real.sqrt (b/(1-b))) z))).const_mul ((-1 : ℝ)^z)
  rw [Real.sqrt_div (le_of_lt hb0)] at ht
  rw [← oscillatorHighest_from_relative (Real.sqrt b) (Real.sqrt (1-b)) hv huvs z p hp]
  apply ht.congr'
  filter_upwards [hB.eventually (eventually_ge_atTop z)] with n hn
  simp only [Pi.div_apply]
  rw [highestUnit_eq_relative (A n) (B n) z p hn]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter

theorem fallingRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => fallingRatio Q z) atTop (𝓝 ((1/2 : ℝ)^z)) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range z,
      ((-(i : ℝ) + 1*(Q : ℝ))/(-(2+(i : ℝ))+2*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range z, (1/2 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(i : ℝ)) (-(2+(i : ℝ))) 1 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range z,
      ((-(i : ℝ) + 1*(Q : ℝ))/(-(2+(i : ℝ))+2*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => fallingRatio Q z) := by
    filter_upwards [eventually_ge_atTop (max z 4)] with Q hQ
    have hzQ : z ≤ Q := le_trans (le_max_left _ _) hQ
    have h4 : 4 ≤ Q := le_trans (le_max_right _ _) hQ
    unfold fallingRatio
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
    simp only [Nat.cast_prod, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hiQ : i ≤ Q := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hzQ
    rw [Nat.cast_sub hiQ, Nat.cast_sub (by omega : i ≤ 2*Q-2),
      Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    congr 1 <;> ring
  have hh := hp.congr' he
  simpa [div_pow] using hh

theorem gramEigenvalueFormula_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => gramEigenvalueFormula Q z) atTop
      (𝓝 ((3*(z : ℝ)-1)*(-1/2 : ℝ)^z)) := by
  have hb : Tendsto (fun Q : ℕ =>
      (3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ))) atTop (𝓝 (3*(z : ℝ)-1)) := by
    have hh := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((z : ℝ)*((z : ℝ)+1))
    simpa [div_eq_mul_inv] using tendsto_const_nhds.sub hh
  have hh := ((fallingRatio_tendsto z).const_mul ((-1 : ℝ)^z)).mul hb
  have he : (-1 : ℝ)^z * (1/2 : ℝ)^z * (3*(z : ℝ)-1) =
      (3*(z : ℝ)-1)*(-1/2 : ℝ)^z := by
    rw [← mul_pow]
    ring
  simpa only [gramEigenvalueFormula, he] using hh

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem threeBody_2 : e 2 < limitBound 2 := by decide +kernel

theorem threeBody_4 : e 4 < limitBound 4 := by decide +kernel

theorem threeBody_5 : e 5 < limitBound 5 := by decide +kernel

theorem threeBody_6 : e 6 < limitBound 6 := by decide +kernel

theorem threeBody_7 : e 7 < limitBound 7 := by decide +kernel

theorem threeBody_8 : e 8 < limitBound 8 := by decide +kernel

theorem threeBody_9 : e 9 < limitBound 9 := by decide +kernel

theorem threeBody_10 : e 10 < limitBound 10 := by decide +kernel

theorem threeBody_11 : e 11 < limitBound 11 := by decide +kernel

theorem threeBody_12 : e 12 < limitBound 12 := by decide +kernel

theorem threeBody_13 : e 13 < limitBound 13 := by decide +kernel

theorem threeBody_14 : e 14 < limitBound 14 := by decide +kernel

theorem threeBody_15 : e 15 < limitBound 15 := by decide +kernel

theorem threeBody_certificate (z : ℕ)
    (hz : z ∈ [2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]) : e z < limitBound z := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact threeBody_2
  · exact threeBody_4
  · exact threeBody_5
  · exact threeBody_6
  · exact threeBody_7
  · exact threeBody_8
  · exact threeBody_9
  · exact threeBody_10
  · exact threeBody_11
  · exact threeBody_12
  · exact threeBody_13
  · exact threeBody_14
  · exact threeBody_15

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_ScalarBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped Topology
open Filter

theorem three_body_real (z : ℕ) (hz : z ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15]) :
    (Certificate.e z : ℝ) <
      (3/2 : ℝ)*(3*(z : ℝ)-1)*(-1/2 : ℝ)^z := by
  have hh : (Certificate.e z : ℝ) < (Certificate.limitBound z : ℝ) :=
    Rat.cast_lt.mpr (Certificate.threeBody_certificate z hz)
  simpa [Certificate.limitBound] using hh

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_OscillatorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators
open Polynomial

theorem sqrtFactorial_pos (n : ℕ) : 0 < sqrtFactorial n := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.factorial_pos n

theorem sqrtFactorial_succ (n : ℕ) :
    sqrtFactorial (n+1) = Real.sqrt ((n : ℝ)+1) * sqrtFactorial n := by
  unfold sqrtFactorial
  rw [Nat.factorial_succ,Nat.cast_mul,Real.sqrt_mul (by positivity)]
  push_cast; rfl

theorem sqrt_choose_factorial (z p : ℕ) (hp : p ≤ z) :
    (z.choose p : ℝ) * monomialNormFactor z p / sqrtFactorial z =
      Real.sqrt (z.choose p : ℝ) := by
  have he : (z.choose p : ℝ) * (p.factorial : ℝ) * ((z-p).factorial : ℝ) = (z.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hp
  have hc : 0 < (z.choose p : ℝ) := by exact_mod_cast Nat.choose_pos hp
  have hs : sqrtFactorial z = Real.sqrt (z.choose p : ℝ) * monomialNormFactor z p := by
    unfold monomialNormFactor sqrtFactorial
    rw [← he,Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
    ring
  have hn := ne_of_gt (sqrtFactorial_pos z)
  apply (div_eq_iff hn).mpr
  rw [hs]
  rw [← mul_assoc,← pow_two,Real.sq_sqrt (le_of_lt hc)]

theorem couplingPolynomial_base_coeff (u v : ℝ) (hu : u ≠ 0) (z p : ℕ) :
    (couplingPolynomial u v z 0).coeff p =
      u^z * ((-v/u)^(z-p) * (z.choose p : ℝ)) := by
  have he : C u * X-C v = C u * (X+C (-v/u)) := by
    rw [mul_add,← C_mul]
    have hc : u*(-v/u) = -v := by field_simp
    rw [hc,C_neg]; ring
  simp only [couplingPolynomial,pow_zero,mul_one,he,mul_pow,← C_pow,coeff_C_mul,coeff_X_add_C_pow]

theorem couplingPolynomial_base_normalized (u v : ℝ) (hu : u ≠ 0) (z p : ℕ) (hp : p ≤ z) :
    couplingPolynomialCoefficient u v z 0 p = oscillatorHighest u v z p := by
  have hz : z=p+(z-p) := by omega
  have hupow : u^z = u^p*u^(z-p) := by rw [← pow_add,← hz]
  unfold couplingPolynomialCoefficient
  rw [couplingPolynomial_base_coeff u v hu]
  simp only [Nat.add_zero,sqrtFactorial,Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,mul_one]
  change _ = (-1 : ℝ)^(z-p)*Real.sqrt (z.choose p : ℝ)*u^p*v^(z-p)
  have he : u^z*(-v/u)^(z-p) = (-1 : ℝ)^(z-p)*u^p*v^(z-p) := by
    rw [hupow,div_pow,neg_eq_neg_one_mul,mul_pow]
    field_simp
  calc
    _ = (u^z*(-v/u)^(z-p))*((z.choose p : ℝ)*monomialNormFactor z p / sqrtFactorial z) := by unfold sqrtFactorial; ring
    _ = _ := by rw [he,sqrt_choose_factorial z p hp]; ring

theorem couplingPolynomial_succ_coeff (u v : ℝ) (z n p : ℕ) :
    (couplingPolynomial u v z (n+1)).coeff p =
      (if p=0 then 0 else v*(couplingPolynomial u v z n).coeff (p-1)) +
        u*(couplingPolynomial u v z n).coeff p := by
  have he : couplingPolynomial u v z (n+1) =
      C v * (couplingPolynomial u v z n * X) + C u * couplingPolynomial u v z n := by
    unfold couplingPolynomial
    rw [pow_succ]
    ring
  rw [he,coeff_add,coeff_C_mul,coeff_C_mul]
  cases p with
  | zero => simp
  | succ p => simp [coeff_mul_X]

theorem couplingPolynomial_coeff_off (u v : ℝ) (hu : u ≠ 0) (z n p : ℕ) (hp : z+n < p) :
    (couplingPolynomial u v z n).coeff p = 0 := by
  induction n generalizing p with
  | zero => rw [couplingPolynomial_base_coeff u v hu,Nat.choose_eq_zero_of_lt (by omega)]; simp
  | succ n ih =>
    rw [couplingPolynomial_succ_coeff,ite_eq_right (by omega : p ≠ 0),ih (p-1) (by omega),ih p (by omega)]
    ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_OscillatorPolynomialLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

 theorem monomialNormFactor_first (T p : ℕ) (hp : 0 < p) :
    monomialNormFactor (T+1) p = Real.sqrt (p : ℝ)*monomialNormFactor T (p-1) := by
  have he : sqrtFactorial p = Real.sqrt (p : ℝ)*sqrtFactorial (p-1) := by
    have hh := sqrtFactorial_succ (p-1)
    have hk : p-1+1=p := by omega
    have hc : ((p-1 : ℕ) : ℝ)+1=p := by exact_mod_cast hk
    rwa [hk,hc] at hh
  unfold monomialNormFactor
  rw [he,show T+1-p=T-(p-1) by omega]
  ring

 theorem monomialNormFactor_second (T p : ℕ) (hp : p ≤ T) :
    monomialNormFactor (T+1) p = Real.sqrt ((T+1-p : ℕ) : ℝ)*monomialNormFactor T p := by
  have hk : T+1-p=(T-p)+1 := by omega
  have hc : ((T-p : ℕ) : ℝ)+1=(T+1-p : ℕ) := by exact_mod_cast hk.symm
  have hf : sqrtFactorial (T+1-p) = Real.sqrt ((T+1-p : ℕ) : ℝ)*sqrtFactorial (T-p) := by
    calc
      _ = sqrtFactorial ((T-p)+1) := by rw [hk]
      _ = _ := by rw [sqrtFactorial_succ,hc]
  unfold monomialNormFactor
  rw [hf]; ring

theorem couplingPolynomialCoefficient_lowering (u v : ℝ) (hu : u ≠ 0)
    (z n p : ℕ) (hp : p ≤ z+n+1) :
    couplingPolynomialCoefficient u v z (n+1) p =
      ((if p=0 then 0 else v*Real.sqrt (p : ℝ)*couplingPolynomialCoefficient u v z n (p-1)) +
       (if p ≤ z+n then u*Real.sqrt ((z+n+1-p : ℕ) : ℝ)*couplingPolynomialCoefficient u v z n p else 0)) /
         Real.sqrt ((n : ℝ)+1) := by
  unfold couplingPolynomialCoefficient
  rw [couplingPolynomial_succ_coeff,sqrtFactorial_succ]
  have ht : z+(n+1)=z+n+1 := by omega
  rw [ht]
  by_cases hp0 : p=0
  · subst p
    simp only [ite_eq_left (by omega : 0 ≤ z+n)]
    rw [monomialNormFactor_second (z+n) 0 (by omega)]
    simp only [Nat.sub_zero]
    simp [div_eq_mul_inv,mul_inv_rev]; ring
  · simp only [ite_eq_right hp0]
    by_cases hpn : p ≤ z+n
    · simp only [ite_eq_left hpn]
      have hfirst := monomialNormFactor_first (z+n) p (by omega)
      have hsecond := monomialNormFactor_second (z+n) p hpn
      rw [add_mul]
      simp only [add_div]
      congr 1
      · rw [hfirst]
        simp only [div_eq_mul_inv,mul_inv_rev]; ring
      · rw [hsecond]
        simp only [div_eq_mul_inv,mul_inv_rev]; ring
    · simp only [ite_eq_right hpn]
      rw [couplingPolynomial_coeff_off u v hu z n p (by omega),mul_zero,add_zero,
        monomialNormFactor_first (z+n) p (by omega)]
      simp only [div_eq_mul_inv,mul_inv_rev]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Array
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem couplingArray_physical (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hTA : z+n ≤ A) (hTB : z+n ≤ B) (i : SpinIndex A B) (hi : i.1.val+i.2.val=z+n) :
    (-1 : ℝ)^z * genericUnitDescendant A B z hA hB n i = couplingArray A B z n i.1.val := by
  induction n generalizing i with
  | zero =>
    rw [genericUnitDescendant_zero]
    let p : Fin (z+1) := ⟨i.1.val,by omega⟩
    have he : i = weightSliceIndex A B z hA hB p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    rw [he]
    change (-1 : ℝ)^z * extendWeightSlice A B z hA hB (fun q => highestUnit A B z q.val)
      (weightSliceIndex A B z hA hB p) = (-1 : ℝ)^z * highestUnit A B z p.val
    rw [extendWeightSlice_at]
  | succ n ih =>
    have hn : n < genericCoupledWeight A B z := by unfold genericCoupledWeight; omega
    have hnreal : (n : ℝ) < genericCoupledWeight A B z := by exact_mod_cast hn
    have hd : Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) ≠ 0 := by positivity
    have he := congrFun (genericUnitDescendant_lowering A B z n hA hB hn) i
    change (∑ j, totalRaise A B j i * genericUnitDescendant A B z hA hB n j) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        genericUnitDescendant A B z hA hB (n+1) i at he
    rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column] at he
    have h1 : (-1 : ℝ)^z *
        (if h : 0 < i.1.val then genericUnitDescendant A B z hA hB n (⟨i.1.val-1,by omega⟩,i.2) *
          ladder A (i.1.val-1) else 0) =
        (if i.1.val=0 then 0 else ladder A (i.1.val-1)*couplingArray A B z n (i.1.val-1)) := by
      by_cases hp : 0 < i.1.val
      · rw [dite_eq_left hp,ite_eq_right (by omega : i.1.val ≠ 0)]
        have hh := ih (by omega) (by omega) (⟨i.1.val-1,by omega⟩,i.2) (by dsimp; omega)
        dsimp at hh
        rw [← hh]; ring
      · rw [dite_eq_right hp,ite_eq_left (by omega : i.1.val=0),mul_zero]
    have h2 : (-1 : ℝ)^z *
        (if h : 0 < i.2.val then genericUnitDescendant A B z hA hB n (i.1,⟨i.2.val-1,by omega⟩) *
          ladder B (i.2.val-1) else 0) =
        (if i.1.val ≤ z+n then ladder B (z+n-i.1.val)*couplingArray A B z n i.1.val else 0) := by
      by_cases hp : 0 < i.2.val
      · rw [dite_eq_left hp,ite_eq_left (by omega : i.1.val ≤ z+n)]
        have hh := ih (by omega) (by omega) (i.1,⟨i.2.val-1,by omega⟩) (by dsimp; omega)
        dsimp at hh
        have hl : ladder B (i.2.val-1) = ladder B (z+n-i.1.val) := congrArg (ladder B) (by omega)
        rw [← hh,hl]; ring
      · rw [dite_eq_right hp,ite_eq_right (by omega : ¬ i.1.val ≤ z+n),mul_zero]
    change _ = (_ + _) / _
    apply (eq_div_iff hd).mpr
    linear_combination h1+h2-(-1 : ℝ)^z*he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_LoweringLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem coupled_denominator_scale_tendsto (S : ℕ → ℕ) (hS : Tendsto S atTop atTop)
    (z n : ℕ) :
    Tendsto (fun j => ((((S j-2*z : ℕ) : ℝ)-(n : ℝ))/(S j : ℝ))) atTop (𝓝 1) := by
  have hself : Tendsto (fun j => (S j : ℝ)/(S j : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [hS.eventually (eventually_ge_atTop 1)] with j hj
    have hn : (S j : ℝ) ≠ 0 := by exact_mod_cast (show S j ≠ 0 by omega)
    rw [div_self hn]
  have ht := spin_fraction_sub_tendsto S S 1 hS hS hself (2*z+n)
  apply ht.congr'
  filter_upwards [hS.eventually (eventually_ge_atTop (2*z+n))] with j hj
  rw [Nat.cast_sub (by omega : 2*z+n ≤ S j),Nat.cast_sub (by omega : 2*z ≤ S j)]
  push_cast
  ring

theorem normalized_ladder_factor_tendsto (C S : ℕ → ℕ) (c : ℝ)
    (hC : Tendsto C atTop atTop) (hS : Tendsto S atTop atTop)
    (hc : Tendsto (fun j => (C j : ℝ)/(S j : ℝ)) atTop (𝓝 c)) (z n k : ℕ) :
    Tendsto (fun j => ladder (C j) k /
      Real.sqrt (((n : ℝ)+1)*(((S j-2*z : ℕ) : ℝ)-n))) atTop
      (𝓝 (Real.sqrt ((((k : ℝ)+1)*c)/((n : ℝ)+1)))) := by
  have hnum := (spin_fraction_sub_tendsto C S c hC hS hc k).const_mul ((k : ℝ)+1)
  have hden := (coupled_denominator_scale_tendsto S hS z n).const_mul ((n : ℝ)+1)
  have ht := (hnum.div hden (by positivity)).sqrt
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [hS.eventually (eventually_ge_atTop 1)] with j hj
  have hp : (S j : ℝ) ≠ 0 := by exact_mod_cast (show S j ≠ 0 by omega)
  simp only [Pi.div_apply]
  have he : (((k : ℝ)+1)*(((C j-k : ℕ) : ℝ)/(S j : ℝ))) /
      (((n : ℝ)+1)*((((S j-2*z : ℕ) : ℝ)-n)/(S j : ℝ))) =
      (((k : ℝ)+1)*((C j-k : ℕ) : ℝ)) /
        (((n : ℝ)+1)*(((S j-2*z : ℕ) : ℝ)-n)) := by field_simp
  rw [he,Real.sqrt_div (by positivity)]
  rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_ArrayLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

theorem couplingArray_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun j => (B j : ℝ)/((A j : ℝ)+B j)) atTop (𝓝 b))
    (z n p : ℕ) (hp : p ≤ z+n) :
    Tendsto (fun j => couplingArray (A j) (B j) z n p) atTop (𝓝 (oscillatorArray b z n p)) := by
  have hS : Tendsto (fun j => A j+B j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_right (A j) (B j)) hA
  induction n generalizing p with
  | zero =>
    exact source_highest_coupling_tendsto A B b hA hB hb0 hb1 hfrac z p (by omega)
  | succ n ih =>
    let d : ℕ → ℝ := fun j => Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight (A j) (B j) z : ℝ)-n))
    have hfirst : Tendsto (fun j => if p=0 then 0 else
        (ladder (A j) (p-1)/d j)*couplingArray (A j) (B j) z n (p-1)) atTop
        (𝓝 (if p=0 then 0 else Real.sqrt ((((p-1 : ℕ)+1 : ℝ)*(1-b))/((n : ℝ)+1))*
          oscillatorArray b z n (p-1))) := by
      by_cases hp0 : p=0
      · simp only [hp0,ite_true]; exact tendsto_const_nhds
      · simp only [hp0,ite_false]
        have hf := normalized_ladder_factor_tendsto A (fun j => A j+B j) (1-b) hA hS
          (by simpa only [Nat.cast_add] using first_spin_fraction_tendsto A B b hA hfrac) z n (p-1)
        exact hf.mul (ih (p-1) (by omega))
    have hsecond : Tendsto (fun j => if p ≤ z+n then
        (ladder (B j) (z+n-p)/d j)*couplingArray (A j) (B j) z n p else 0) atTop
        (𝓝 (if p ≤ z+n then Real.sqrt ((((z+n-p : ℕ)+1 : ℝ)*b)/((n : ℝ)+1))*
          oscillatorArray b z n p else 0)) := by
      by_cases hpn : p ≤ z+n
      · simp only [hpn,ite_true]
        have hf := normalized_ladder_factor_tendsto B (fun j => A j+B j) b hB hS
          (by simpa only [Nat.cast_add] using hfrac) z n (z+n-p)
        exact hf.mul (ih p hpn)
      · simp only [hpn,ite_false]; exact tendsto_const_nhds
    have ht := hfirst.add hsecond
    apply ht.congr'
    exact Filter.Eventually.of_forall (fun j => by
      change (if p=0 then 0 else (ladder (A j) (p-1)/d j)*couplingArray (A j) (B j) z n (p-1)) +
        (if p ≤ z+n then (ladder (B j) (z+n-p)/d j)*couplingArray (A j) (B j) z n p else 0) = _
      change _ = ((if p=0 then 0 else _) + (if p ≤ z+n then _ else 0))/d j
      split_ifs <;> ring)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem oscillatorArray_polynomial (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (z n p : ℕ) (hp : p ≤ z+n) :
    oscillatorArray b z n p =
      couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z n p := by
  have hu : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb0)
  induction n generalizing p with
  | zero => exact (couplingPolynomial_base_normalized _ _ hu z p (by omega)).symm
  | succ n ih =>
    have hf (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
        Real.sqrt ((((k : ℝ)+1)*c)/((n : ℝ)+1)) =
          Real.sqrt c * Real.sqrt ((k : ℝ)+1) / Real.sqrt ((n : ℝ)+1) := by
      rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity)]
      ring
    have hfirst :
        (if p=0 then 0 else Real.sqrt ((((p-1 : ℕ)+1 : ℝ)*(1-b))/((n : ℝ)+1))*oscillatorArray b z n (p-1)) =
        (if p=0 then 0 else Real.sqrt (1-b)*Real.sqrt (p : ℝ)*
          couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z n (p-1)) / Real.sqrt ((n : ℝ)+1) := by
      by_cases hp0 : p=0
      · simp only [hp0,ite_true,zero_div]
      · simp only [hp0,ite_false]
        have hk : ((p-1 : ℕ) : ℝ)+1=p := by exact_mod_cast (show p-1+1=p by omega)
        rw [ih (p-1) (by omega),hf (1-b) (by linarith),hk]
        ring
    have hsecond :
        (if p ≤ z+n then Real.sqrt ((((z+n-p : ℕ)+1 : ℝ)*b)/((n : ℝ)+1))*oscillatorArray b z n p else 0) =
        (if p ≤ z+n then Real.sqrt b*Real.sqrt ((z+n+1-p : ℕ) : ℝ)*
          couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z n p else 0) / Real.sqrt ((n : ℝ)+1) := by
      by_cases hpn : p ≤ z+n
      · simp only [hpn,ite_true]
        have hk : ((z+n-p : ℕ) : ℝ)+1=(z+n+1-p : ℕ) := by
          exact_mod_cast (show z+n-p+1=z+n+1-p by omega)
        rw [ih p hpn,hf b (le_of_lt hb0),hk]
        ring
      · simp only [hpn,ite_false,zero_div]
    rw [oscillatorArray,couplingPolynomialCoefficient_lowering _ _ hu z n p (by omega),hfirst,hsecond,← add_div]

theorem source_coupling_polynomial_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun j => (B j : ℝ)/((A j : ℝ)+B j)) atTop (𝓝 b))
    (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun j => couplingArray (A j) (B j) z (T-z) p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z (T-z) p)) := by
  rw [← oscillatorArray_polynomial b hb0 hb1 z (T-z) p (by omega)]
  exact couplingArray_tendsto A B b hA hB hb0 hb1 hfrac z (T-z) p (by omega)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_PhysicalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem physicalCouplingCoefficient_eq_array (A B z T p : ℕ)
    (hz : z ≤ T) (hp : p ≤ T) (hA : T ≤ A) (hB : T ≤ B) :
    physicalCouplingCoefficient A B z T p = couplingArray A B z (T-z) p := by
  rw [physicalCouplingCoefficient,dite_eq_left ⟨hz,hp,hA,hB⟩]
  exact couplingArray_physical A B z (T-z) (by omega) (by omega) (by omega) (by omega)
    (⟨p,by omega⟩,⟨T-p,by omega⟩) (by dsimp; omega)

theorem source_physical_coupling_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun j => (B j : ℝ)/((A j : ℝ)+B j)) atTop (𝓝 b))
    (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun j => physicalCouplingCoefficient (A j) (B j) z T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z (T-z) p)) := by
  apply (source_coupling_polynomial_tendsto A B b hA hB hb0 hb1 hfrac z T p hz hp).congr'
  filter_upwards [hA.eventually (eventually_ge_atTop T),hB.eventually (eventually_ge_atTop T)] with j hjA hjB
  exact (physicalCouplingCoefficient_eq_array (A j) (B j) z T p hz hp hjA hjB).symm

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Specializations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem affine_spin_tendsto (a c : ℕ) (ha : 0 < a) :
    Tendsto (fun Q : ℕ => a*Q-c) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (k+c)] with Q hQ
  have hm : Q ≤ a*Q := by
    simpa using Nat.mul_le_mul_right Q (show 1 ≤ a by omega)
  omega

theorem affine_spin_fraction_tendsto (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun Q : ℕ => ((b*Q-d : ℕ) : ℝ)/(((a*Q-c : ℕ) : ℝ)+((b*Q-d : ℕ) : ℝ)))
      atTop (𝓝 ((b : ℝ)/((a : ℝ)+b))) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have ht : Tendsto (fun Q : ℕ => (-(d : ℝ)+(b : ℝ)*Q)/
      (-(c : ℝ)-(d : ℝ)+((a : ℝ)+b)*Q)) atTop (𝓝 ((b : ℝ)/((a : ℝ)+b))) :=
    tendsto_add_mul_div_add_mul_atTop_nhds (-(d : ℝ)) (-(c : ℝ)-(d : ℝ)) (b : ℝ) (by positivity)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (c+d)] with Q hQ
  have hmA : Q ≤ a*Q := by simpa using Nat.mul_le_mul_right Q (show 1 ≤ a by omega)
  have hmB : Q ≤ b*Q := by simpa using Nat.mul_le_mul_right Q (show 1 ≤ b by omega)
  rw [Nat.cast_sub (by omega : c ≤ a*Q),Nat.cast_sub (by omega : d ≤ b*Q)]
  push_cast
  congr 1 <;> ring

theorem source_threeBody_coupling_tendsto (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun Q : ℕ => physicalCouplingCoefficient (2*Q-2) Q z T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p)) := by
  have hA := affine_spin_tendsto 2 2 (by omega)
  have hB : Tendsto (fun Q : ℕ => Q) atTop atTop := tendsto_id
  have hf : Tendsto (fun Q : ℕ => (Q : ℝ)/(((2*Q-2 : ℕ) : ℝ)+Q)) atTop (𝓝 (1/3 : ℝ)) := by
    have h := affine_spin_fraction_tendsto 2 1 2 0 (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have hh := source_physical_coupling_tendsto (fun Q => 2*Q-2) (fun Q => Q) (1/3) hA hB
    (by norm_num) (by norm_num) hf z T p hz hp
  norm_num at hh ⊢
  exact hh

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_ErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem physical_list_sum_tendsto {I : Type*} (l : List I) (f : ℕ → I → ℝ) (g : I → ℝ)
    (h : ∀ i ∈ l, Tendsto (fun Q => f Q i) atTop (𝓝 (g i))) :
    Tendsto (fun Q => (l.map (f Q)).sum) atTop (𝓝 ((l.map g).sum)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_ErrorCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem sourceAlpha_factor (t : ℕ) (e : ℕ × ℕ × ℤ) :
    sourceAlpha t e = (e.2.2 : ℝ)/(10^7) * alphaRadical t e.1 e.2.1 := rfl

theorem real_list_sum_scale {I : Type*} (l : List I) (c : ℝ) (f : I → ℝ) :
    (l.map (fun i => c*f i)).sum = c*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_IntegerPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators
open Polynomial

theorem U_general_sum (c z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    U c z T p = ∑ h ∈ Finset.range (p+1),
      (-1 : ℤ)^(z-h) * (z.choose h : ℤ) * ((T-z).choose (p-h) : ℤ) * (c : ℤ)^(p-h) := by
  unfold U
  rw [ite_eq_left ⟨hz,hp⟩,← List.sum_toFinset _ (List.nodup_range.filter _)]
  simp only [List.toFinset_filter,List.toFinset_range]
  apply Finset.sum_subset
  · intro h hh
    simp only [Finset.mem_filter,Finset.mem_range] at hh ⊢
    omega
  · intro h hh hn
    simp only [Finset.mem_range,Finset.mem_filter,decide_eq_true_eq,not_and] at hh hn
    by_cases hhz : h ≤ z
    · have hbound : ¬ p+z ≤ T+h := hn (by omega)
      rw [Nat.choose_eq_zero_of_lt (by omega : T-z < p-h)]
      simp
    · rw [Nat.choose_eq_zero_of_lt (by omega : z < h)]
      simp

theorem weightedIntegerCouplingPolynomial_coeff (c z n p : ℕ) (hp : p ≤ z+n) :
    (weightedIntegerCouplingPolynomial c z n).coeff p = U c z (z+n) p := by
  rw [U_general_sum c z (z+n) p (by omega) hp]
  simp only [Nat.add_sub_cancel_left]
  unfold weightedIntegerCouplingPolynomial
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro h hh
  have hneg : (Polynomial.X-1 : Polynomial ℤ) = Polynomial.X+C (-1) := by simp [sub_eq_add_neg]
  rw [hneg,coeff_X_add_C_pow]
  rw [show (C (c : ℤ)*Polynomial.X+1 : Polynomial ℤ)^n = ((Polynomial.X+1)^n).comp (C (c : ℤ)*Polynomial.X) by simp]
  rw [comp_C_mul_X_coeff]
  rw [show (Polynomial.X+1 : Polynomial ℤ) = Polynomial.X+C 1 by simp,coeff_X_add_C_pow]
  simp
  ring

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_RankTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem realOuter_quadratic {I : Type*} [Fintype I] (u v x : I → ℝ) :
    dotProduct x (realOuter u v *ᵥ x) = dotProduct x u * dotProduct x v := by
  simp only [dotProduct,Matrix.mulVec,realOuter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem threeSpinProjector_trace (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
    Matrix.trace (threeSpinProjector Q hQ z * M) =
      ∑ n : Fin (coupledWeight Q z.val+1),
        dotProduct (normalizedCoupledDescendant Q z.val hQ (by omega) n.val)
          (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n.val) := by
  let B := coupledBasisMatrix Q hQ
  have he : Matrix.trace (threeSpinProjector Q hQ z * M) =
      Matrix.trace (coupledSelector Q z * (Bᵀ*M*B)) := by
    change Matrix.trace (B*coupledSelector Q z*Bᵀ*M) = _
    calc
      _ = Matrix.trace ((B*coupledSelector Q z)*(Bᵀ*M)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Bᵀ*M)*(B*coupledSelector Q z)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Bᵀ*M*B)*coupledSelector Q z) := by simp only [Matrix.mul_assoc]
      _ = _ := Matrix.trace_mul_comm _ _
  rw [he]
  unfold coupledSelector
  simp only [Matrix.trace,Matrix.diag,Matrix.diagonal_mul]
  rw [Fintype.sum_sigma]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Matrix.mul_apply,Matrix.transpose_apply,B,coupledBasisMatrix,Matrix.mulVec,dotProduct]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_TraceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem threeBodyInner_tendsto (z T t : ℕ) (entries : List (ℕ × ℕ × ℤ)) (hz : z ≤ T) :
    Tendsto (fun Q => threeBodyInner (physicalCouplingCoefficient (2*Q-2) Q) z T t entries)
      atTop (𝓝 (threeBodyInner (fun z T p => couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T t entries)) := by
  apply physical_list_sum_tendsto
  intro e he
  by_cases h : e.1+e.2.1=T
  · simp only [ite_eq_left h]
    exact tendsto_const_nhds.mul (source_threeBody_coupling_tendsto z T e.1 hz (by omega))
  · simp only [ite_eq_right h]
    exact tendsto_const_nhds

theorem physicalThreeBodyTraceFormula_tendsto (z : ℕ) :
    Tendsto (fun Q => physicalThreeBodyTraceFormula Q z) atTop
      (𝓝 (limitThreeBodyTraceFormula z)) := by
  unfold physicalThreeBodyTraceFormula limitThreeBodyTraceFormula threeBodyTraceFormula
  apply physical_list_sum_tendsto
  intro row hrow
  apply physical_list_sum_tendsto
  intro T hT
  have h : z ≤ T ∧ row.1 ≤ T := by
    simp only [List.mem_filter,decide_eq_true_eq, max_le_iff] at hT
    exact hT.2
  exact ((tendsto_const_nhds.mul (source_threeBody_coupling_tendsto z T row.1 h.1 h.2)).mul
    (threeBodyInner_tendsto z T row.1 row.2.2 h.1)).add
    ((threeBodyInner_tendsto z T row.1 row.2.2 h.1).pow 2)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_PhysicalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairOrbitalUnit_dot (Q p j : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q)
    (v : PairOrbitalIndex Q → ℝ) :
    dotProduct v (pairOrbitalUnit Q p j) = v (⟨p,hp⟩,⟨j,by omega⟩) := by
  classical
  simp only [dotProduct,pairOrbitalUnit,mul_ite,mul_one,mul_zero]
  have he : ∀ i : PairOrbitalIndex Q, (i.1.val=p ∧ i.2.val=j) ↔ i=(⟨p,hp⟩,⟨j,by omega⟩) := by
    intro i
    constructor
    · rintro ⟨h1,h2⟩; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · intro h; subst i; exact ⟨rfl,rfl⟩
  simp_rw [he]
  simp

theorem threeBodyLevelMatrix_quadratic (Q t T : ℕ) (ell : ℤ) (entries : List (ℕ × ℕ × ℤ))
    (v : PairOrbitalIndex Q → ℝ) :
    dotProduct v (threeBodyLevelMatrix Q t T ell entries *ᵥ v) =
      2*((ell : ℝ)/10^7)*dotProduct v (pairOrbitalUnit Q t (T-t))*
        dotProduct v (threeBodyLevelVector Q t T entries) +
      (dotProduct v (threeBodyLevelVector Q t T entries))^2 := by
  simp only [threeBodyLevelMatrix,Matrix.add_mulVec,Matrix.smul_mulVec,
    dotProduct_add,dotProduct_smul,realOuter_quadratic,smul_eq_mul]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_TraceReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem phasedThreeDescendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n : ℕ)
    (i : PairOrbitalIndex Q) (hi : i.1.val+i.2.val ≠ z.val+n) :
    phasedThreeDescendant Q hQ z n i = 0 := by
  have hh := genericUnitDescendant_off (2*Q-2) Q z.val n (by omega) (by omega) i hi
  change (-1 : ℝ)^z.val * genericUnitDescendant (2*Q-2) Q z.val (by omega) (by omega) n i = 0
  rw [hh,mul_zero]

theorem phasedThreeDescendant_at_level (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (T p j : ℕ)
    (hz : z.val ≤ T) (hT : T ≤ Q) (hpj : p+j=T) :
    phasedThreeDescendant Q hQ z (T-z.val) (⟨p,by omega⟩,⟨j,by omega⟩) =
      physicalCouplingCoefficient (2*Q-2) Q z.val T p := by
  rw [physicalCouplingCoefficient,dite_eq_left ⟨hz,by omega,by omega,hT⟩]
  have hj : T-p=j := by omega
  subst j
  rfl

theorem threeBodyLevelVector_dot {Q : ℕ} (v : PairOrbitalIndex Q → ℝ) (t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) :
    dotProduct v (threeBodyLevelVector Q t T entries) =
      (entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e *
        dotProduct v (pairOrbitalUnit Q e.1 e.2.1) else 0)).sum := by
  induction entries with
  | nil => simp [threeBodyLevelVector]
  | cons e es ih =>
    simp only [threeBodyLevelVector,List.map_cons,List.sum_cons] at ih ⊢
    rw [dotProduct_add,ih]
    by_cases h : e.1+e.2.1=T
    · simp [h,dotProduct_smul,mul_comm]
    · simp [h]

theorem phasedThreeDescendant_unit_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n p j : ℕ)
    (h : p+j ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n) (pairOrbitalUnit Q p j) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  simp only [pairOrbitalUnit]
  split_ifs with he
  · rw [phasedThreeDescendant_off Q hQ z n i (by omega),zero_mul]
  · exact mul_zero _

theorem threeBodyLevelVector_descendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) (h : T ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n) (threeBodyLevelVector Q t T entries) = 0 := by
  rw [threeBodyLevelVector_dot]
  have he : entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e *
      dotProduct (phasedThreeDescendant Q hQ z n) (pairOrbitalUnit Q e.1 e.2.1) else 0) = entries.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro e he
    split_ifs with hT
    · rw [phasedThreeDescendant_unit_off Q hQ z n e.1 e.2.1 (by omega),mul_zero]
    · rfl
  rw [he]
  simp

theorem threeBodyLevelVector_descendant (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) (hz : z.val ≤ T) (hT : T ≤ Q) :
    dotProduct (phasedThreeDescendant Q hQ z (T-z.val)) (threeBodyLevelVector Q t T entries) =
      threeBodyInner (physicalCouplingCoefficient (2*Q-2) Q) z.val T t entries := by
  rw [threeBodyLevelVector_dot]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  split_ifs with h
  · rw [pairOrbitalUnit_dot Q e.1 e.2.1 (by omega) (by omega),
      phasedThreeDescendant_at_level Q hQ z T e.1 e.2.1 hz hT h]
  · rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_LevelTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

 theorem phasedThreeDescendant_quadratic (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n : ℕ)
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
    dotProduct (phasedThreeDescendant Q hQ z n) (M *ᵥ phasedThreeDescendant Q hQ z n) =
      dotProduct (normalizedCoupledDescendant Q z.val hQ (by omega) n)
        (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n) := by
  simp only [phasedThreeDescendant,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  have hs : ((-1 : ℝ)^z.val)^2=1 := by rw [← pow_mul,mul_comm z.val 2,pow_mul]; norm_num
  nlinarith only [congrArg (fun s : ℝ => s * dotProduct
    (normalizedCoupledDescendant Q z.val hQ (by omega) n)
    (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n)) hs]

theorem threeBodyLevelMatrix_descendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (h : T ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n)
      (threeBodyLevelMatrix Q t T ell entries *ᵥ phasedThreeDescendant Q hQ z n) = 0 := by
  rw [threeBodyLevelMatrix_quadratic,threeBodyLevelVector_descendant_off Q hQ z n t T entries h]
  ring

theorem threeBodyLevelMatrix_descendant (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (hz : z.val ≤ T) (hT : T ≤ Q) (ht : t ≤ T) :
    dotProduct (phasedThreeDescendant Q hQ z (T-z.val))
      (threeBodyLevelMatrix Q t T ell entries *ᵥ phasedThreeDescendant Q hQ z (T-z.val)) =
      physicalThreeBodyLevel Q z.val T t ell entries := by
  rw [threeBodyLevelMatrix_quadratic,threeBodyLevelVector_descendant Q hQ z t T entries hz hT,
    pairOrbitalUnit_dot Q t (T-t) (by omega) (by omega),
    phasedThreeDescendant_at_level Q hQ z T t (T-t) hz hT (by omega)]
  rfl

theorem threeBodyLevelMatrix_trace (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (hT : T ≤ Q) (ht : t ≤ T) :
    Matrix.trace (threeSpinProjector Q hQ z * threeBodyLevelMatrix Q t T ell entries) =
      if z.val ≤ T then physicalThreeBodyLevel Q z.val T t ell entries else 0 := by
  classical
  rw [threeSpinProjector_trace]
  simp_rw [← phasedThreeDescendant_quadratic]
  by_cases hz : z.val ≤ T
  · rw [ite_eq_left hz]
    have hn : T-z.val < coupledWeight Q z.val+1 := by unfold coupledWeight; omega
    rw [Finset.sum_eq_single (⟨T-z.val,hn⟩ : Fin (coupledWeight Q z.val+1))]
    · exact threeBodyLevelMatrix_descendant Q hQ z t T ell entries hz hT ht
    · intro n hn' hne
      apply threeBodyLevelMatrix_descendant_off
      intro he
      apply hne
      exact Fin.ext (by dsimp; omega)
    · simp
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro n hn
    exact threeBodyLevelMatrix_descendant_off Q hQ z n.val t T ell entries (by omega)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_PolynomialCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Polynomial

theorem threeBody_scaled_polynomial (u w : ℝ) (hw : w^2=2) (hw0 : w ≠ 0) (z n : ℕ) :
    couplingPolynomial u (w*u) z n = C (u^(z+n)*w^z) *
      ((Certificate.weightedIntegerCouplingPolynomial 2 z n).map (Int.castRingHom ℝ)).comp (C w⁻¹*X) := by
  have h2 : (2 : ℝ)*w⁻¹=w := by
    field_simp
    nlinarith only [hw]
  simp only [Certificate.weightedIntegerCouplingPolynomial,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_sub,Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,Polynomial.map_C,
    Int.coe_castRingHom,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.sub_comp,Polynomial.add_comp,
    Polynomial.X_comp,Polynomial.C_comp,Polynomial.one_comp]
  norm_num only [Nat.cast_ofNat,Int.cast_natCast]
  rw [show C (2 : ℝ)*(C w⁻¹*X) = C w*X by rw [← mul_assoc,← C_mul,h2]]
  have he : C u*X-C (w*u) = C (u*w)*(C w⁻¹*X-1) := by
    have hc : u*w*w⁻¹=u := by field_simp
    simp only [mul_sub,← mul_assoc,← C_mul,mul_one,hc]
    rw [mul_comm w u]
  have hf : C (w*u)*X+C u = C u*(C w*X+1) := by
    simp only [mul_add,← mul_assoc,← C_mul,mul_one]
    rw [mul_comm w u]
  unfold couplingPolynomial
  rw [he,hf,mul_pow,mul_pow,← C_pow,← C_pow]
  simp only [pow_add,mul_pow,C_mul]
  ring

theorem threeBody_polynomialCoefficient_factorial (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    couplingPolynomialCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p =
      (Certificate.U 2 z T p : ℝ) * (Real.sqrt (1/3))^T *
      (Real.sqrt 2)^z / (Real.sqrt 2)^p *
      sqrtFactorial p * sqrtFactorial (T-p) / (sqrtFactorial z*sqrtFactorial (T-z)) := by
  have hs : Real.sqrt (2/3) = Real.sqrt 2 * Real.sqrt (1/3) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hT : z+(T-z)=T := by omega
  unfold couplingPolynomialCoefficient
  rw [hs,threeBody_scaled_polynomial _ _ (Real.sq_sqrt (by norm_num)) (by positivity),
    coeff_C_mul,comp_C_mul_X_coeff,coeff_map,
    Certificate.weightedIntegerCouplingPolynomial_coeff 2 z (T-z) p (by omega)]
  simp only [Int.coe_castRingHom,hT,monomialNormFactor,inv_pow]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_Radical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem threeBodyRadical_factorial (z T p : ℕ) :
    threeBodyRadical z T p =
      (Real.sqrt (1/3))^T * (Real.sqrt 2)^z / (Real.sqrt 2)^p *
      sqrtFactorial p * sqrtFactorial (T-p) / (sqrtFactorial z*sqrtFactorial (T-z)) := by
  let a := (Real.sqrt (1/3))^T * (Real.sqrt 2)^z / (Real.sqrt 2)^p *
      sqrtFactorial p * sqrtFactorial (T-p) / (sqrtFactorial z*sqrtFactorial (T-z))
  have ha : 0 ≤ a := by dsimp [a]; unfold sqrtFactorial; positivity
  have hs : a^2 = (2 : ℝ)^((z : ℤ)-p) *
    ((p.factorial : ℝ)*((T-p).factorial : ℝ) /
      ((3 : ℝ)^T * (z.factorial : ℝ)*((T-z).factorial : ℝ))) := by
    dsimp [a]
    simp only [div_pow,mul_pow,sqrtFactorial]
    have hr (c : ℝ) (hc : 0 ≤ c) (n : ℕ) : (Real.sqrt c ^ n)^2 = c^n := by
      rw [← pow_mul,mul_comm n 2,pow_mul,Real.sq_sqrt hc]
    rw [hr _ (by norm_num),hr _ (by norm_num),hr _ (by norm_num)]
    simp only [Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zpow_natCast,div_pow,one_pow]
    ring
  change Real.sqrt _ = a
  rw [← hs,Real.sqrt_sq ha]

theorem source_threeBody_radical_coefficient (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    couplingPolynomialCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p =
      (Certificate.U 2 z T p : ℝ) * threeBodyRadical z T p := by
  rw [threeBody_polynomialCoefficient_factorial z T p hz hp,threeBodyRadical_factorial]
  ring

theorem threeBody_alpha_radical_cancel (z T t p j : ℕ) (hT : p+j=T) :
    alphaRadical t p j * threeBodyRadical z T p = threeBodyRadical z T t := by
  have hj : T-p=j := by omega
  have he : ((p : ℤ)-t)+((z : ℤ)-p)=(z : ℤ)-t := by omega
  have hs : (alphaRadical t p j * threeBodyRadical z T p)^2 = (threeBodyRadical z T t)^2 := by
    simp only [alphaRadical,threeBodyRadical,mul_pow]
    repeat rw [Real.sq_sqrt (by positivity)]
    rw [hT,hj]
    calc
      _ = ((2 : ℝ)^((p : ℤ)-t)*(2 : ℝ)^((z : ℤ)-p)) *
        ((t.factorial : ℝ)*(T-t).factorial/(3^T*z.factorial*(T-z).factorial)) := by field_simp
      _ = _ := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),he]
  have hl : 0 ≤ alphaRadical t p j * threeBodyRadical z T p := by
    unfold alphaRadical threeBodyRadical; positivity
  have hr : 0 ≤ threeBodyRadical z T t := Real.sqrt_nonneg _
  nlinarith only [hs,hl,hr]

theorem threeBodyRadical_sq_choose (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    (threeBodyRadical z T p)^2 =
      (2 : ℝ)^z * (T.choose z : ℝ) / ((3 : ℝ)^T * (2 : ℝ)^p * (T.choose p : ℝ)) := by
  have hc (k : ℕ) (hk : k ≤ T) : (T.choose k : ℝ) * (k.factorial : ℝ) * ((T-k).factorial : ℝ) = T.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hcp : (T.choose p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.choose_pos hp))
  unfold threeBodyRadical
  rw [Real.sq_sqrt (by positivity),zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_natCast]
  apply (eq_div_iff (by positivity : (3 : ℝ)^T*2^p*(T.choose p : ℝ) ≠ 0)).mpr
  have hzfac := hc z hz
  have hpfac := hc p hp
  field_simp
  nlinarith only [hzfac,hpfac]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_TraceCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

 theorem threeBodyInner_certificate (z T t : ℕ) (hz : z ≤ T)
    (entries : List (ℕ × ℕ × ℤ)) :
    threeBodyInner (fun z T p => couplingPolynomialCoefficient
      (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T t entries =
      (threeBodyRadical z T t / 10^7) * (Certificate.X entries z T : ℝ) := by
  induction entries with
  | nil => simp [threeBodyInner,Certificate.X]
  | cons e es ih =>
    simp only [threeBodyInner,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    change _ = (threeBodyRadical z T t/10^7) *
      (((if e.1+e.2.1=T then e.2.2*Certificate.U 2 z T e.1 else 0)+Certificate.X es z T : ℤ) : ℝ)
    rw [Int.cast_add]
    by_cases he : e.1+e.2.1=T
    · rw [ite_eq_left he,ite_eq_left he,sourceAlpha_factor,
        source_threeBody_radical_coefficient z T e.1 hz (by omega)]
      simp only [Int.cast_mul]
      have hc := threeBody_alpha_radical_cancel z T t e.1 e.2.1 he
      calc
        _ = ((e.2.2 : ℝ)*(Certificate.U 2 z T e.1 : ℝ)/10^7) *
            (alphaRadical t e.1 e.2.1 * threeBodyRadical z T e.1) +
            threeBodyRadical z T t/10^7 * (Certificate.X es z T : ℝ) := by ring
        _ = _ := by rw [hc]; ring
    · simp [he]

theorem threeBodyLevel_certificate (z T : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (hz : z ≤ T) (ht : row.1 ≤ T) :
    (let a := threeBodyInner (fun z T p => couplingPolynomialCoefficient
      (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T row.1 row.2.2;
      2*((row.2.1 : ℝ)/10^7)*couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) row.1*a+a^2) =
      (1/(10^14) : ℝ)*(rationalThreeBodyLevel z T row : ℝ) := by
  dsimp only
  rw [threeBodyInner_certificate z T row.1 hz,
    source_threeBody_radical_coefficient z T row.1 hz ht]
  calc
    _ = (1/(10^14) : ℝ)*(threeBodyRadical z T row.1)^2 * (Certificate.X row.2.2 z T : ℝ) *
        ((Certificate.X row.2.2 z T : ℝ)+2*(row.2.1 : ℝ)*(Certificate.U 2 z T row.1 : ℝ)) := by ring
    _ = _ := by
      rw [threeBodyRadical_sq_choose z T row.1 hz ht]
      unfold rationalThreeBodyLevel
      push_cast
      ring

theorem source_threeBody_trace_certificate_identity (z : ℕ) :
    limitThreeBodyTraceFormula z = (Certificate.e z : ℝ) := by
  unfold limitThreeBodyTraceFormula threeBodyTraceFormula
  have he : Certificate.rows.map (fun row =>
      (((List.range 16).filter (fun T => max z row.1 ≤ T)).map (fun T =>
      let a := threeBodyInner (fun z T p => couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T row.1 row.2.2;
      2*((row.2.1 : ℝ)/10^7)*couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) row.1*a+a^2)).sum) =
      Certificate.rows.map (fun row => (((List.range 16).filter (fun T => max z row.1 ≤ T)).map
        (fun T => (1/(10^14) : ℝ)*(rationalThreeBodyLevel z T row : ℝ))).sum) := by
    apply List.map_congr_left; intro row hrow
    apply congrArg List.sum
    apply List.map_congr_left; intro T hT
    simp only [List.mem_filter,decide_eq_true_eq,max_le_iff] at hT
    exact threeBodyLevel_certificate z T row hT.2.1 hT.2.2
  rw [he]
  simp_rw [real_list_sum_scale]
  unfold Certificate.e rationalThreeBodyLevel
  push_cast
  simp only [List.map_map,Function.comp_def]
  push_cast
  simp only [List.map_map,Function.comp_def]
  push_cast
  ring

 theorem source_physical_threeBody_trace_formula_tendsto (z : ℕ) :
    Filter.Tendsto (fun Q => physicalThreeBodyTraceFormula Q z) Filter.atTop
      (nhds (Certificate.e z : ℝ)) := by
  rw [← source_threeBody_trace_certificate_identity]
  exact physicalThreeBodyTraceFormula_tendsto z

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_PhysicalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Topology

 theorem trace_mul_list_sum {I : Type*} [Fintype I] (P : Matrix I I ℝ)
    (l : List (Matrix I I ℝ)) :
    Matrix.trace (P*l.sum) = (l.map (fun M => Matrix.trace (P*M))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.sum_cons,List.map_cons,Matrix.mul_add,Matrix.trace_add,ih]

 theorem list_filter_sum_if {I : Type*} (l : List I) (p q : I → Prop)
    [DecidablePred p] [DecidablePred q] (f : I → ℝ) :
    ((l.filter p).map (fun i => if q i then f i else 0)).sum =
      ((l.filter (fun i => p i ∧ q i)).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp,hq,ih]

theorem source_physical_threeBody_trace_identity (Q : ℕ) (hQ : 15 ≤ Q) (z : Fin (Q+1)) :
    Matrix.trace (threeSpinProjector Q (by omega) z * physicalThreeBodyMatrix Q) =
      physicalThreeBodyTraceFormula Q z.val := by
  unfold physicalThreeBodyMatrix
  rw [trace_mul_list_sum]
  simp only [List.map_map,Function.comp_def]
  unfold physicalThreeBodyTraceFormula threeBodyTraceFormula
  apply congrArg List.sum
  apply List.map_congr_left
  intro row hrow
  rw [trace_mul_list_sum]
  simp only [List.map_map,Function.comp_def]
  have he : (((List.range 16).filter (fun T => row.1 ≤ T)).map
      (fun T => Matrix.trace (threeSpinProjector Q (by omega) z * threeBodyLevelMatrix Q row.1 T row.2.1 row.2.2))) =
      (((List.range 16).filter (fun T => row.1 ≤ T)).map
        (fun T => if z.val ≤ T then physicalThreeBodyLevel Q z.val T row.1 row.2.1 row.2.2 else 0)) := by
    apply List.map_congr_left
    intro T hT
    simp only [List.mem_filter,List.mem_range,decide_eq_true_eq] at hT
    exact threeBodyLevelMatrix_trace Q (by omega) z row.1 T row.2.1 row.2.2 (by omega) hT.2
  rw [he,list_filter_sum_if]
  simp only [physicalThreeBodyLevel,max_le_iff,and_comm]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_TraceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem threeBodyDimensionRatio_tendsto (z : ℕ) :
    Tendsto (fun Q => threeBodyDimensionRatio Q z) atTop (𝓝 (3/2 : ℝ)) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds (-1-2*(z : ℝ)) (-1 : ℝ) 3 (d := 2) (by norm_num)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext Q
  unfold threeBodyDimensionRatio
  congr 1 <;> ring

theorem source_threeBody_trace_strict_eventually (z : ℕ)
    (hz : z ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15]) :
    ∀ᶠ Q : ℕ in atTop, physicalThreeBodyTraceFormula Q z <
      threeBodyDimensionRatio Q z * gramEigenvalueFormula Q z := by
  have h := ((threeBodyDimensionRatio_tendsto z).mul (gramEigenvalueFormula_tendsto z)).sub
    (source_physical_threeBody_trace_formula_tendsto z)
  have hl : 0 < (3/2 : ℝ)*((3*(z : ℝ)-1)*(-1/2 : ℝ)^z)-(Certificate.e z : ℝ) := by
    have hh := three_body_real z hz
    nlinarith only [hh]
  exact ((tendsto_order.mp h).1 0 hl).mono (fun Q hQ => by linarith)

theorem eventually_list_all {I : Type*} (l : List I) (P : ℕ → I → Prop)
    (h : ∀ i ∈ l, ∀ᶠ Q in atTop, P Q i) : ∀ᶠ Q in atTop, ∀ i ∈ l, P Q i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    filter_upwards [h a (by simp),ih (fun i hi => h i (by simp [hi]))] with Q ha hl
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ha
    · exact hl i hi

theorem source_threeBody_physical_traces_strict_eventually_oai :
    ∀ᶠ Q : ℕ in atTop, ∃ hQ : 15 ≤ Q, ∀ z : Fin (Q+1),
      z.val ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15] →
      Matrix.trace (threeSpinProjector Q (by omega) z * physicalThreeBodyMatrix Q) <
        threeBodyDimensionRatio Q z.val * gramEigenvalueFormula Q z.val := by
  have hall := eventually_list_all [2,4,5,6,7,8,9,10,11,12,13,14,15]
    (fun Q z => physicalThreeBodyTraceFormula Q z < threeBodyDimensionRatio Q z * gramEigenvalueFormula Q z)
    source_threeBody_trace_strict_eventually
  filter_upwards [eventually_ge_atTop 15,hall] with Q hQ h
  refine ⟨hQ,?_⟩
  intro z hz
  rw [source_physical_threeBody_trace_identity Q hQ]
  exact h z.val hz

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.source_threeBody_physical_traces_strict_eventually_oai := @OAI.Laughlin.Spin.source_threeBody_physical_traces_strict_eventually_oai
