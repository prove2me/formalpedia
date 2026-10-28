-- Prove2me | solution 1 for OAI.Laughlin.Fock.averagedFourTransferError_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:31:48.613436+00:00
-- url     : https://prove2.me/submissions/1216c1ec-66fd-4f44-9577-da3874bee1f8

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
-- module Solutions.OAIQ047_LA.Laughlin_Pair_FactorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter

theorem modeFactor_sq_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => (Q.descFactorial x : ℝ)/(Q : ℝ)^x)
      atTop (𝓝 1) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range x,
      ((-(i : ℝ)+1*(Q : ℝ))/(0+1*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range x, (1/1 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(i : ℝ)) 0 1 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range x,
      ((-(i : ℝ)+1*(Q : ℝ))/(0+1*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => (Q.descFactorial x : ℝ)/(Q : ℝ)^x) := by
    filter_upwards [eventually_ge_atTop x] with Q hQ
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hd : (Q : ℝ)^x = ∏ _i ∈ Finset.range x, (Q : ℝ) := by simp
    rw [hd, ← Finset.prod_div_distrib]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ Q)]
      congr 1 <;> ring
  simpa using hp.congr' he

theorem pairFactor_inv_sq_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => ((2*Q-2).descFactorial p : ℝ)/((2 : ℝ)*Q)^p)
      atTop (𝓝 1) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range p,
      ((-(2+(i : ℝ))+2*(Q : ℝ))/(0+2*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range p, (2/2 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(2+(i : ℝ))) 0 2 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range p,
      ((-(2+(i : ℝ))+2*(Q : ℝ))/(0+2*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => ((2*Q-2).descFactorial p : ℝ)/((2 : ℝ)*Q)^p) := by
    filter_upwards [eventually_ge_atTop (p+2)] with Q hQ
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hd : ((2 : ℝ)*Q)^p = ∏ _i ∈ Finset.range p, (2 : ℝ)*Q := by simp
    rw [hd, ← Finset.prod_div_distrib]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ 2*Q-2), Nat.cast_sub (by omega : 2 ≤ 2*Q)]
      push_cast
      congr 1 <;> ring
  simpa using hp.congr' he

theorem modeFactor_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => modeFactor Q x) atTop (𝓝 1) := by
  simpa [modeFactor] using (modeFactor_sq_tendsto x).sqrt

theorem pairFactor_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => pairFactor Q p) atTop (𝓝 1) := by
  have h := ((pairFactor_inv_sq_tendsto p).inv₀ (by norm_num)).sqrt
  simpa [pairFactor, inv_div] using h

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_LocalDiagonalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem localDiagonals_tendsto (L : ℕ) :
    Tendsto (localDiagonals L) atTop (𝓝 (fun _ => (1 : ℝ))) := by
  apply tendsto_pi_nhds.mpr
  intro A
  have h : Tendsto (fun Q => ∏ i ∈ A, modeFactor Q i.val) atTop (𝓝 (∏ _i ∈ A, (1 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact modeFactor_tendsto i.val
  simpa [localDiagonals] using h

theorem localInverseDiagonals_tendsto (L : ℕ) :
    Tendsto (fun Q => fun A : Finset (Fin (L+1)) => (localDiagonals L Q A)⁻¹)
      atTop (𝓝 (fun _ => (1 : ℝ))) := by
  apply tendsto_pi_nhds.mpr
  intro A
  simpa using ((tendsto_pi_nhds.mp (localDiagonals_tendsto L)) A).inv₀ (by norm_num)

theorem localMetricDiagonals_tendsto (L : ℕ) :
    Tendsto (fun Q => fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2)
      atTop (𝓝 (fun _ => (1 : ℝ))) := by
  apply tendsto_pi_nhds.mpr
  intro A
  simpa using ((tendsto_pi_nhds.mp (localInverseDiagonals_tendsto L)) A).pow 2

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_LocalMetricLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem localMetricError_tendsto (L : ℕ) :
    Tendsto (localMetricError L) atTop (𝓝 0) := by
  have h := ((localMetricDiagonals_tendsto L).sub
    (tendsto_const_nhds (x := fun _ : Finset (Fin (L+1)) => (1 : ℝ)))).norm
  change Tendsto (fun Q : ℕ => ‖(fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2) -
    (fun _ : Finset (Fin (L+1)) => (1 : ℝ))‖) atTop (𝓝 0)
  simpa only [sub_self,norm_zero] using h

end Laughlin.Fock

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

theorem source_fourBody_inner_coupling_tendsto (r T p : ℕ) (hr : r ≤ T) (hp : p ≤ T) :
    Tendsto (fun Q : ℕ => physicalCouplingCoefficient Q Q r T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) r (T-r) p)) := by
  have hf : Tendsto (fun Q : ℕ => (Q : ℝ)/((Q : ℝ)+Q)) atTop (𝓝 (1/2 : ℝ)) := by
    have h := affine_spin_fraction_tendsto 1 1 0 0 (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have hh := source_physical_coupling_tendsto (fun Q => Q) (fun Q => Q) (1/2) tendsto_id tendsto_id
    (by norm_num) (by norm_num) hf r T p hr hp
  norm_num at hh ⊢
  exact hh

theorem source_fourBody_outer_coupling_tendsto (r z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun Q : ℕ => physicalCouplingCoefficient (2*Q-2) (2*Q-2*r) z T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) z (T-z) p)) := by
  have hf : Tendsto (fun Q : ℕ => ((2*Q-2*r : ℕ) : ℝ)/
      (((2*Q-2 : ℕ) : ℝ)+((2*Q-2*r : ℕ) : ℝ))) atTop (𝓝 (1/2 : ℝ)) := by
    have h := affine_spin_fraction_tendsto 2 2 2 (2*r) (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have hh := source_physical_coupling_tendsto (fun Q => 2*Q-2) (fun Q => 2*Q-2*r) (1/2)
    (affine_spin_tendsto 2 2 (by omega)) (affine_spin_tendsto 2 (2*r) (by omega))
    (by norm_num) (by norm_num) hf z T p hz hp
  norm_num at hh ⊢
  exact hh

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_CoefficientLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem source_fourBody_coefficient_tendsto (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    Tendsto (fun Q : ℕ => fourBodyCoefficient Q r D T p j k) atTop
      (𝓝 (fourBodyLimitCoefficient r D T p j k)) := by
  by_cases hr : r ≤ j+k
  · simp only [fourBodyCoefficient,fourBodyLimitCoefficient,ite_eq_left hr]
    have hI := source_fourBody_inner_coupling_tendsto r (j+k) j hr (by omega)
    have hO := source_fourBody_outer_coupling_tendsto r (D-r) (T-r) p (by omega) (by omega)
    have he : T-r-(D-r)=T-D := by omega
    rw [he] at hO
    exact (tendsto_const_nhds.mul hI).mul hO
  · simp only [fourBodyCoefficient,fourBodyLimitCoefficient,ite_eq_right hr]
    exact tendsto_const_nhds

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

theorem fourErrorEntry_tendsto (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (hr : r ≤ D) (hs : s ≤ D) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1) :
    Tendsto (fun Q => fourErrorEntry Q D r s t e f) atTop (𝓝 (fourErrorLimitEntry D r s t e f)) := by
  unfold fourErrorEntry fourErrorLimitEntry
  dsimp only
  by_cases hD : D ≤ e.1+e.2.1+(f.1+f.2.1-t)
  · simp only [ite_eq_left hD]
    exact (tendsto_const_nhds.mul
      (source_fourBody_coefficient_tendsto r D _ e.1 e.2.1 _ hr hD rfl)).mul
      (source_fourBody_coefficient_tendsto s D _ f.1 f.2.1 _ hs hD (by omega))
  · simp only [ite_eq_right hD]; exact tendsto_const_nhds

theorem physical_list_sum_tendsto {I : Type*} (l : List I) (f : ℕ → I → ℝ) (g : I → ℝ)
    (h : ∀ i ∈ l, Tendsto (fun Q => f Q i) atTop (𝓝 (g i))) :
    Tendsto (fun Q => (l.map (f Q)).sum) atTop (𝓝 ((l.map g).sum)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))

theorem source_rows_admissible : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2,
    row.1 ≤ e.1+e.2.1 := by decide

theorem physicalFourError_tendsto (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D) :
    Tendsto (fun Q => physicalFourError Q D r s) atTop (𝓝 (limitFourError D r s)) := by
  apply Filter.Tendsto.neg
  apply physical_list_sum_tendsto
  intro row hrow
  apply physical_list_sum_tendsto
  intro e he
  apply physical_list_sum_tendsto
  intro f hf
  exact fourErrorEntry_tendsto D r s row.1 e f hr hs
    (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_SourceIntegerPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators
open Polynomial

theorem U_one_sum (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    U 1 z T p = ∑ h ∈ Finset.range (p+1),
      (-1 : ℤ)^(z-h) * (z.choose h : ℤ) * ((T-z).choose (p-h) : ℤ) := by
  unfold U
  rw [ite_eq_left ⟨hz,hp⟩]
  simp only [Int.natCast_one,one_pow,mul_one]
  rw [← List.sum_toFinset _ (List.nodup_range.filter _)]
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

theorem integerCouplingPolynomial_coeff (z n p : ℕ) (hp : p ≤ z+n) :
    (integerCouplingPolynomial z n).coeff p = U 1 z (z+n) p := by
  rw [U_one_sum z (z+n) p (by omega) hp]
  simp only [Nat.add_sub_cancel_left]
  unfold integerCouplingPolynomial
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro h hh
  have hneg : (Polynomial.X-1 : Polynomial ℤ) = Polynomial.X+C (-1) := by simp [sub_eq_add_neg]
  have hpos : (Polynomial.X+1 : Polynomial ℤ) = Polynomial.X+C 1 := by simp
  rw [hneg,hpos,coeff_X_add_C_pow,coeff_X_add_C_pow]
  simp

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_SourceEqualSpinPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators
open Polynomial

theorem equalSpin_polynomial (u : ℝ) (z n : ℕ) :
    couplingPolynomial u u z n = C (u^(z+n)) *
      (Certificate.integerCouplingPolynomial z n).map (Int.castRingHom ℝ) := by
  simp only [couplingPolynomial,Certificate.integerCouplingPolynomial,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_sub,Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,pow_add,C_mul,C_pow]
  rw [show C u * X-C u = C u*(X-1) by ring,
    show C u * X+C u = C u*(X+1) by ring,mul_pow,mul_pow]
  ring

theorem equalSpin_polynomialCoefficient (u : ℝ) (z n p : ℕ) (hp : p ≤ z+n) :
    couplingPolynomialCoefficient u u z n p =
      u^(z+n) * (Certificate.U 1 z (z+n) p : ℝ) *
        sqrtFactorial p * sqrtFactorial (z+n-p) / (sqrtFactorial z * sqrtFactorial n) := by
  unfold couplingPolynomialCoefficient
  rw [equalSpin_polynomial,coeff_C_mul,coeff_map,Certificate.integerCouplingPolynomial_coeff z n p hp]
  simp only [Int.coe_castRingHom,monomialNormFactor]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_FactorialCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem source_fourBody_factorial_coefficient (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) (hr : r ≤ j+k) :
    fourBodyLimitCoefficient r D T p j k =
      Real.sqrt 2 * (Real.sqrt (1/2))^(j+k+(T-r)) * (Certificate.V r D T p j k : ℝ) *
      sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
        (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D)) := by
  have hi : r+(j+k-r)=j+k := by omega
  have ho : (D-r)+(T-D)=T-r := by omega
  have hk : j+k-j=k := by omega
  have hb : T-r-p=j+k-r := by omega
  rw [fourBodyLimitCoefficient,ite_eq_left hr,
    equalSpin_polynomialCoefficient _ r (j+k-r) j (by omega),
    equalSpin_polynomialCoefficient _ (D-r) (T-D) p (by omega)]
  rw [hi,ho,hk,hb]
  simp only [Certificate.V,ite_eq_left hr,Int.cast_mul]
  rw [pow_add]
  field_simp [ne_of_gt (sqrtFactorial_pos r),ne_of_gt (sqrtFactorial_pos (D-r)),
    ne_of_gt (sqrtFactorial_pos (T-D)),ne_of_gt (sqrtFactorial_pos (j+k-r))]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RadicalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem fourBodyRadical_factorial (r D T p j k : ℕ) (hr : r ≤ T) :
    fourBodyRadical r D T p j k =
      Real.sqrt 2 * (Real.sqrt (1/2))^(j+k+(T-r)) *
      sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
        (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D)) := by
  let m := j+k+(T-r)
  have hm : (1 : ℤ)-(j : ℤ)-k-T+r = 1-(m : ℤ) := by
    dsimp [m]
    simp only [Nat.cast_sub hr]
    omega
  have hp : (2 : ℝ)^((1 : ℤ)-(j : ℤ)-k-T+r) = 2*(1/2 : ℝ)^m := by
    rw [hm,zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),zpow_one,zpow_natCast]
    simp [div_eq_mul_inv]
  let a := Real.sqrt 2 * (Real.sqrt (1/2))^m *
    sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
      (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D))
  have ha : 0 ≤ a := by dsimp [a]; unfold sqrtFactorial; positivity
  have hs : a^2 = (2 : ℝ)^((1 : ℤ)-(j : ℤ)-k-T+r) *
    ((j.factorial : ℝ)*(k.factorial : ℝ)*(p.factorial : ℝ) /
      ((r.factorial : ℝ)*((D-r).factorial : ℝ)*((T-D).factorial : ℝ))) := by
    rw [hp]
    dsimp [a]
    simp only [div_pow,mul_pow,sqrtFactorial]
    rw [show ((Real.sqrt (1/2))^m)^2 = (1/2 : ℝ)^m by
      rw [← pow_mul,mul_comm m 2,pow_mul,Real.sq_sqrt (by norm_num)]]
    simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sq_sqrt (Nat.cast_nonneg _)]
    ring_nf
    norm_num
  change Real.sqrt _ = a
  rw [← hs,Real.sqrt_sq ha]

theorem source_fourBody_radical_coefficient (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    fourBodyLimitCoefficient r D T p j k =
      (Certificate.V r D T p j k : ℝ) * fourBodyRadical r D T p j k := by
  by_cases hr : r ≤ j+k
  · rw [source_fourBody_factorial_coefficient r D T p j k hrD hDT hT hr,
      fourBodyRadical_factorial r D T p j k (by omega)]
    ring
  · simp [fourBodyLimitCoefficient,Certificate.V,hr]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RadicalCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem source_Y_radical_cancellation (D r s t p j q l : ℕ)
    (hor : Odd r) (hos : Odd s) (he : t ≤ p+j) (hf : t ≤ q+l) :
    alphaRadical t p j * alphaRadical t q l *
      fourBodyRadical r D (p+j+(q+l-t)) p j (q+l-t) *
      fourBodyRadical s D (p+j+(q+l-t)) q l (p+j-t) =
    Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l := by
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  let e : ℤ := 1-2*(T : ℤ)+p+q-t+((r+s)/2 : ℕ)
  have hT : p+j+k=T := rfl
  have hT' : q+l+i=T := by dsimp [i,k,T]; omega
  have hTr : (p : ℤ)+j+k=T := by exact_mod_cast hT
  have hTr' : (q : ℤ)+l+i=T := by exact_mod_cast hT'
  have heven : (((r+s)/2 : ℕ) : ℤ)*2=(r : ℤ)+s := by
    rcases hor with ⟨a,ha⟩; rcases hos with ⟨b,hb⟩
    omega
  have hex : ((p : ℤ)-t)+((q : ℤ)-t)+((1 : ℤ)-j-k-T+r)+((1 : ℤ)-l-i-T+s)=e*2 := by
    dsimp [e]; omega
  have hpowers : (2 : ℝ)^((p : ℤ)-t) * (2 : ℝ)^((q : ℤ)-t) *
      (2 : ℝ)^((1 : ℤ)-j-k-T+r) * (2 : ℝ)^((1 : ℤ)-l-i-T+s) = ((2 : ℝ)^e)^2 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),hex,zpow_mul]
    norm_num
  let F : ℝ := ((i.factorial : ℝ)*(k.factorial : ℝ)*(t.factorial : ℝ))^2 /
    ((r.factorial : ℝ)*((D-r).factorial : ℝ)*(s.factorial : ℝ)*((D-s).factorial : ℝ)*((T-D).factorial : ℝ)^2)
  have hsq : (alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k *
      fourBodyRadical s D T q l i)^2 =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l)^2 := by
    simp only [alphaRadical,fourBodyRadical,mul_pow]
    have hc0 : 0 ≤ sourceCopyWeight D r * sourceCopyWeight D s := by
      unfold sourceCopyWeight; positivity
    rw [Real.sq_sqrt hc0]
    repeat rw [Real.sq_sqrt (by positivity)]
    change (2^((p : ℤ)-t)*((t.factorial : ℝ)*i.factorial/(p.factorial*j.factorial))) *
      (2^((q : ℤ)-t)*((t.factorial : ℝ)*k.factorial/(q.factorial*l.factorial))) *
      (2^((1 : ℤ)-j-k-T+r)*((j.factorial : ℝ)*k.factorial*p.factorial /
        (r.factorial*(D-r).factorial*(T-D).factorial))) *
      (2^((1 : ℤ)-l-i-T+s)*((l.factorial : ℝ)*i.factorial*q.factorial /
        (s.factorial*(D-s).factorial*(T-D).factorial))) = _
    calc
      _ = (2^((p : ℤ)-t)*2^((q : ℤ)-t)*2^((1 : ℤ)-j-k-T+r)*2^((1 : ℤ)-l-i-T+s))*F := by
        dsimp [F]
        field_simp
      _ = ((2 : ℝ)^e)^2*F := by rw [hpowers]
      _ = _ := by
        dsimp [F,sourceYFactor,sourceCopyWeight]
        change ((2 : ℝ)^e)^2 * _ = (1/((r.factorial : ℝ)*(D-r).factorial) *
          (1/((s.factorial : ℝ)*(D-s).factorial))) *
          ((2 : ℝ)^e * ((i.factorial : ℝ)*k.factorial*t.factorial/(T-D).factorial))^2
        field_simp
  have hl : 0 ≤ alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k *
      fourBodyRadical s D T q l i := by unfold alphaRadical fourBodyRadical; positivity
  have hr : 0 ≤ Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l := by
    unfold sourceYFactor; positivity
  nlinarith only [hsq,hl,hr]

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

theorem fourErrorLimitEntry_certificate (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (hr : r ≤ D) (hs : s ≤ D) (hor : Odd r) (hos : Odd s)
    (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1) :
    fourErrorLimitEntry D r s t e f =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yEntry D r s t e f : ℝ) := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp only at he hf ⊢
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  have hT' : q+l+i=T := by dsimp [i,k,T]; omega
  by_cases hD : D ≤ T
  · have heq : fourErrorLimitEntry D r s t (p,j,a) (q,l,b) =
        sourceAlpha t (p,j,a) * sourceAlpha t (q,l,b) *
          fourBodyLimitCoefficient r D T p j k * fourBodyLimitCoefficient s D T q l i := by
      simp only [fourErrorLimitEntry]; exact ite_eq_left hD
    rw [heq,sourceAlpha_factor,sourceAlpha_factor,
      source_fourBody_radical_coefficient r D T p j k hr hD rfl,
      source_fourBody_radical_coefficient s D T q l i hs hD hT']
    dsimp only
    calc
      _ = ((a : ℝ)*(b : ℝ)*(Certificate.V r D T p j k : ℝ)*(Certificate.V s D T q l i : ℝ)/(10^14)) *
          (alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k * fourBodyRadical s D T q l i) := by ring
      _ = ((a : ℝ)*(b : ℝ)*(Certificate.V r D T p j k : ℝ)*(Certificate.V s D T q l i : ℝ)/(10^14)) *
          (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)*sourceYFactor D r s t p j q l) := by
        rw [source_Y_radical_cancellation D r s t p j q l hor hos he hf]
      _ = _ := by
        simp only [Certificate.yEntry]
        rw [ite_eq_left hD]
        push_cast
        dsimp [sourceYFactor,i,k,T]
        ring
  · simp only [fourErrorLimitEntry,Certificate.yEntry]
    rw [ite_eq_right hD,ite_eq_right hD]
    simp

theorem real_list_sum_scale {I : Type*} (l : List I) (c : ℝ) (f : I → ℝ) :
    (l.map (fun i => c*f i)).sum = c*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem fourErrorLimitRow_certificate (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hrow : row ∈ Certificate.rows) :
    fourErrorLimitRow D r s row =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yRow D r s row : ℝ) := by
  unfold fourErrorLimitRow
  have he : ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      fourErrorLimitEntry D r s row.1 e f =
        (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
          (Certificate.yEntry D r s row.1 e f : ℝ) := by
    intro e he f hf
    exact fourErrorLimitEntry_certificate D r s row.1 e f hr hs hor hos
      (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)
  calc
    _ = (row.2.2.map (fun e => (row.2.2.map (fun f =>
        (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
          (Certificate.yEntry D r s row.1 e f : ℝ))).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left; intro e he'
      apply congrArg List.sum
      apply List.map_congr_left; intro f hf'
      exact he e he' f hf'
    _ = _ := by
      simp_rw [real_list_sum_scale]
      unfold Certificate.yRow
      push_cast
      simp only [List.map_map,Function.comp_def]
      push_cast
      simp only [List.map_map,Function.comp_def]

theorem source_fourBody_error_certificate_identity (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) :
    limitFourError D r s = Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) *
      (Certificate.Y D r s : ℝ) := by
  unfold limitFourError
  have he : Certificate.rows.map (fourErrorLimitRow D r s) = Certificate.rows.map (fun row =>
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yRow D r s row : ℝ)) := by
    apply List.map_congr_left; intro row hrow
    exact fourErrorLimitRow_certificate D r s hr hs hor hos row hrow
  rw [he,real_list_sum_scale]
  unfold Certificate.Y
  push_cast
  simp only [List.map_map,Function.comp_def]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Scaled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem copyWeight_nonneg (D : ℕ) (i : Fin ((D+1)/2)) : 0 ≤ (copyWeight D i : ℝ) := by
  unfold copyWeight
  positivity

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_ErrorMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Matrix Topology
open Filter

theorem sourceCopyWeight_certificate (D : ℕ) (i : Fin ((D+1)/2)) :
    sourceCopyWeight D (Certificate.copyLabel i) = (Certificate.copyWeight D i : ℝ) := by
  simp [sourceCopyWeight,Certificate.copyWeight]

theorem source_fourBody_error_matrix (D : ℕ) (i j : Fin ((D+1)/2)) :
    limitFourError D (Certificate.copyLabel i) (Certificate.copyLabel j) = Certificate.scaledError D i j := by
  have hi : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hj : Certificate.copyLabel j ≤ D := by unfold Certificate.copyLabel; have := j.isLt; omega
  have hoi : Odd (Certificate.copyLabel i) := ⟨i.val,by unfold Certificate.copyLabel; omega⟩
  have hoj : Odd (Certificate.copyLabel j) := ⟨j.val,by unfold Certificate.copyLabel; omega⟩
  rw [source_fourBody_error_certificate_identity D _ _ hi hj hoi hoj,
    sourceCopyWeight_certificate,sourceCopyWeight_certificate,
    Real.sqrt_mul (Certificate.copyWeight_nonneg D i)]
  simp only [Certificate.scaledError,Certificate.weightSqrtDiagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.map_apply,Certificate.errorRational,Rat.coe_castHom]
  ring

theorem physicalFourError_certificate_tendsto (D : ℕ) (i j : Fin ((D+1)/2)) :
    Tendsto (fun Q => physicalFourError Q D (Certificate.copyLabel i) (Certificate.copyLabel j))
      atTop (𝓝 (Certificate.scaledError D i j)) := by
  rw [← source_fourBody_error_matrix D i j]
  apply physicalFourError_tendsto D
  · unfold Certificate.copyLabel; have := i.isLt; omega
  · unfold Certificate.copyLabel; have := j.isLt; omega

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_TransferConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

theorem physicalFourBeta_tendsto (r D : ℕ) (hrD : r ≤ D) (b : LocalFourIndex D) :
    Tendsto (fun Q => physicalFourBeta Q r D b) atTop
      (𝓝 (fourBodyLimitCoefficient r D D b.val.1.val b.val.2.1.val b.val.2.2.val)) := by
  have hs := source_fourBody_coefficient_tendsto r D D b.val.1.val b.val.2.1.val b.val.2.2.val
    hrD (le_refl _) b.property.1
  have hp := pairFactor_tendsto b.val.1.val
  have hj := modeFactor_tendsto b.val.2.1.val
  have hk := modeFactor_tendsto b.val.2.2.val
  have hh := (hs.mul hp).div (hj.mul hk) (by norm_num)
  simp only [mul_one,div_one] at hh
  apply hh.congr
  intro Q
  rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_PhysicalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix

theorem physicalLimitError_eq (D : ℕ) : physicalLimitError D = Certificate.scaledError D := by
  ext i j
  exact Spin.source_fourBody_error_matrix D i j

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_MiddleLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix Topology
open Filter Spin

theorem fourDimensionRatio_tendsto (D : ℕ) : Tendsto (fun Q => fourDimensionRatio Q D) atTop (𝓝 2) := by
  have hi : Tendsto (fun Q : ℕ => (Q : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hn := (tendsto_const_nhds (x := (4 : ℝ))).sub (hi.const_mul (1+2*(D : ℝ)))
  have hd := (tendsto_const_nhds (x := (2 : ℝ))).sub hi
  have hh := hn.div hd (by norm_num : (2 : ℝ)-0 ≠ 0)
  have he : (fun Q : ℕ => fourDimensionRatio Q D) =ᶠ[atTop]
      (fun Q => (4-(1+2*(D : ℝ))*(Q : ℝ)⁻¹)/(2-(Q : ℝ)⁻¹)) := by
    filter_upwards [eventually_ge_atTop 1] with Q hQ
    have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
    unfold fourDimensionRatio
    field_simp
    ring
  apply Tendsto.congr' he.symm
  norm_num at hh
  apply hh.congr
  intro Q
  rfl

theorem finiteFourMiddle_tendsto (D : ℕ) (i j : Fin ((D+1)/2)) :
    Tendsto (fun Q => finiteFourMiddle Q D i j) atTop (𝓝 (limitFourMiddle D i j)) := by
  have he := physicalFourError_certificate_tendsto D i j
  rw [← physicalLimitError_eq D] at he
  unfold finiteFourMiddle limitFourMiddle
  apply Tendsto.sub _ he
  by_cases hij : i=j
  · subst j
    by_cases hi : Certificate.copyLabel i=1
    · simpa [Matrix.diagonal_apply,hi,Certificate.certificateDiagonal,Matrix.map_apply] using
        (fourDimensionRatio_tendsto D).add_const (3/10^6 : ℝ)
    · simp [hi,Certificate.certificateDiagonal,Matrix.map_apply]
  · simp [hij,Certificate.certificateDiagonal,Matrix.map_apply]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_MatrixMetricError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem entrySum_tendsto {I : Type*} [Fintype I] (R : ℕ → I → I → ℝ) (S : I → I → ℝ)
    (hR : ∀ i j, Tendsto (fun Q => R Q i j) atTop (𝓝 (S i j))) :
    Tendsto (fun Q => entrySum (R Q)) atTop (𝓝 (entrySum S)) := by
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact (hR i j).abs

theorem matrixMetricError_tendsto {I : Type*} [Fintype I] (L : ℕ)
    (R : ℕ → I → I → ℝ) (S : I → I → ℝ)
    (hR : ∀ i j, Tendsto (fun Q => R Q i j) atTop (𝓝 (S i j))) :
    Tendsto (fun Q => matrixMetricError L Q (R Q) S) atTop (𝓝 0) := by
  have hd := entrySum_tendsto (fun Q i j => R Q i j-S i j) (fun _ _ => 0)
    (fun i j => by simpa using (hR i j).sub_const (S i j))
  have hr := entrySum_tendsto R S hR
  have h := hd.add ((localMetricError_tendsto L).mul hr)
  simpa [matrixMetricError,entrySum] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_TransferCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

theorem finiteLocalFourMatrix_tendsto (D : ℕ) (a b : LocalFourIndex D) :
    Tendsto (fun Q => finiteLocalFourMatrix Q D a b) atTop (𝓝 (limitLocalFourMatrix D a b)) := by
  unfold finiteLocalFourMatrix limitLocalFourMatrix copyQuadraticMatrix
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  have hiD : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hjD : Certificate.copyLabel j ≤ D := by unfold Certificate.copyLabel; have := j.isLt; omega
  exact ((finiteFourMiddle_tendsto D i j).mul (physicalFourBeta_tendsto _ D hiD a)).mul
    (physicalFourBeta_tendsto _ D hjD b)

theorem fourBodyRho_tendsto (D : ℕ) : Tendsto (fourBodyRho D) atTop (𝓝 0) := by
  have h := (matrixMetricError_tendsto 24 (fun Q => finiteLocalFourMatrix Q D)
    (limitLocalFourMatrix D) (finiteLocalFourMatrix_tendsto D)).mul_const
      ((Fintype.card (LocalFourIndex D) : ℝ)^2)
  change Tendsto (fun Q => matrixMetricError 24 Q (finiteLocalFourMatrix Q D)
    (limitLocalFourMatrix D) * (Fintype.card (LocalFourIndex D) : ℝ)^2) atTop (𝓝 0)
  simpa using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_UniformTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

theorem uniformFourBodyRho_tendsto : Tendsto uniformFourBodyRho atTop (𝓝 0) := by
  have h := tendsto_finsetSum (s := Finset.range 24) (fun D hD => fourBodyRho_tendsto D)
  change Tendsto (fun Q => ∑ D ∈ Finset.range 24, fourBodyRho D Q) atTop (𝓝 0)
  simpa using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_HaarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Topology

theorem averagedFourTransferError_tendsto_oai :
    Filter.Tendsto averagedFourTransferError Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun Q => 24 * uniformFourBodyRho Q) Filter.atTop (𝓝 0)
  simpa only [mul_zero] using uniformFourBodyRho_tendsto.const_mul 24

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.averagedFourTransferError_tendsto_oai := @OAI.Laughlin.Fock.averagedFourTransferError_tendsto_oai
