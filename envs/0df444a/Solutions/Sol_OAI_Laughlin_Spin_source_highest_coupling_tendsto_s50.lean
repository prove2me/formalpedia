-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_highest_coupling_tendsto_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:11:38.592242+00:00
-- url     : https://prove2.me/submissions/cc6b92e7-ae4f-429c-bc14-463a3e0d00c5

import Mathlib
import Definitions.Def_OAIQ050L015
import Theorems.Thm_OAI_Laughlin_Spin_relativeHighestNorm_tendsto_s50
import Theorems.Thm_OAI_Laughlin_Spin_relativeHighest_tendsto_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_OscillatorHighestNormalization
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_HighestCouplingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

theorem source_highest_coupling_tendsto_s50_oai (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b))
    (z p : ℕ) (hp : p ≤ z) :
    Tendsto (fun n => (-1 : ℝ)^z * highestUnit (A n) (B n) z p) atTop
      (𝓝 (oscillatorHighest (Real.sqrt b) (Real.sqrt (1-b)) z p)) := by
  have huvs : (Real.sqrt b)^2+(Real.sqrt (1-b))^2=1 := by
    rw [Real.sq_sqrt (le_of_lt hb0),Real.sq_sqrt (by linarith)]; ring
  have hv : 0 < Real.sqrt (1-b) := Real.sqrt_pos.mpr (by linarith)
  have ht := ((relativeHighest_tendsto_s50 A B b hA hB hb0 hb1 hfrac z p hp).div
    (relativeHighestNorm_tendsto_s50 A B b hA hB hb0 hb1 hfrac z)
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

theorem solution : type_of% @OAI.Laughlin.Spin.source_highest_coupling_tendsto_s50_oai := @OAI.Laughlin.Spin.source_highest_coupling_tendsto_s50_oai
