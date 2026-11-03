-- Prove2me | solution 1 for OAI.Laughlin.Spin.relativeHighest_tendsto_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:07:35.831119+00:00
-- url     : https://prove2.me/submissions/19a8acdc-9a23-4992-b436-fbb7dc8f949b

import Mathlib
import Definitions.Def_OAIQ050L014
import Definitions.Def_OAIQ050L015

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

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_RelativeHighest
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

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_OscillatorHighest
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

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_ScaleLimit
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_HighestCouplingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

theorem relativeHighest_tendsto_s50_oai (A B : ℕ → ℕ) (b : ℝ)
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

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.relativeHighest_tendsto_s50_oai := @OAI.Laughlin.Spin.relativeHighest_tendsto_s50_oai
