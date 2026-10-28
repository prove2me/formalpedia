-- Prove2me | solution 1 for OAI.Laughlin.Fock.source_fourBody_physical_L
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:39:36.625414+00:00
-- url     : https://prove2.me/submissions/cba89a44-fdd2-4eb0-aa4e-d200b20aa93c

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
-- module Solutions.OAIQ047_LA.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem mixed_car {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j + create j * annihilate i =
      (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x =
      (if i = j then (1 : ℂ) else 0) • x
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  by_cases h : i = j
  · subst j
    simp [mode, LinearMap.proj]
  · simp [mode, LinearMap.proj, h]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_NormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_create {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j = delta i j • (1 : Module.End ℂ (Space Q)) -
      create j * annihilate i := by
  exact eq_sub_of_add_eq (mixed_car i j)

theorem normal_order_two_inner {Q : ℕ} (a b c d : Fin (Q+1)) :
    annihilate b * annihilate a * create c * create d =
      delta a c • (annihilate b * create d) -
      delta b c • (annihilate a * create d) +
      create c * annihilate b * annihilate a * create d := by
  calc
    _ = annihilate b * (annihilate a * create c) * create d := by noncomm_ring
    _ = delta a c • (annihilate b * create d) -
        (annihilate b * create c) * annihilate a * create d := by
      rw [annihilate_create]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one]
      noncomm_ring
    _ = _ := by
      rw [annihilate_create b c]
      simp only [sub_mul, smul_mul_assoc, one_mul]
      noncomm_ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_NormalOrderFour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem normal_order_two_one {Q : ℕ} (a b d : Fin (Q+1)) :
    annihilate b * annihilate a * create d =
      delta a d • annihilate b - delta b d • annihilate a +
        create d * annihilate b * annihilate a := by
  calc
    _ = annihilate b * (annihilate a * create d) := by noncomm_ring
    _ = delta a d • annihilate b - (annihilate b * create d) * annihilate a := by
      rw [annihilate_create]
      simp only [mul_sub, mul_smul_comm, mul_one]
      noncomm_ring
    _ = _ := by
      rw [annihilate_create b d]
      simp only [sub_mul, smul_mul_assoc, one_mul]
      noncomm_ring

theorem normal_order_four {Q : ℕ} (a b c d : Fin (Q+1)) :
    annihilate b * annihilate a * create c * create d =
      delta a c • (delta b d • (1 : Module.End ℂ (Space Q))) -
      delta b c • (delta a d • (1 : Module.End ℂ (Space Q))) -
      delta a c • (create d * annihilate b) +
      delta b c • (create d * annihilate a) +
      delta a d • (create c * annihilate b) -
      delta b d • (create c * annihilate a) +
      create c * create d * annihilate b * annihilate a := by
  rw [normal_order_two_inner, annihilate_create b d, annihilate_create a d]
  have h : create c * annihilate b * annihilate a * create d =
      create c * (annihilate b * annihilate a * create d) := by noncomm_ring
  rw [h, normal_order_two_one]
  simp only [smul_sub, mul_add, mul_sub, mul_smul_comm]
  noncomm_ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_PairNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_vacuum {Q : ℕ} (i : Fin (Q+1)) : annihilate i (1 : Space Q) = 0 := by
  simp [annihilate]

theorem two_annihilate_two_create {Q : ℕ} (a b i j : Fin (Q+1)) :
    annihilate b (annihilate a (create i (create j (1 : Space Q)))) =
      (delta a i*delta b j-delta b i*delta a j) • (1 : Space Q) := by
  have h := LinearMap.congr_fun (normal_order_four a b i j) (1 : Space Q)
  simpa [Module.End.mul_apply, annihilate_vacuum, smul_smul, sub_smul] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_CARReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_create_apply (Q : ℕ) (a b : Fin (Q+1)) (x : Space Q) :
    annihilate a (create b x) = delta a b • x - create b (annihilate a x) := by
  have h := LinearMap.congr_fun (annihilate_create a b) x
  simpa only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply] using h

theorem annihilate_three_create (Q : ℕ) (a x y z : Fin (Q+1)) :
    annihilate a (create x (create y (create z (1 : Space Q)))) =
      delta a x • create y (create z (1 : Space Q)) -
      delta a y • create x (create z (1 : Space Q)) +
      delta a z • create x (create y (1 : Space Q)) := by
  simp only [annihilate_create_apply,annihilate_vacuum,map_zero,sub_zero,map_sub,map_smul]
  abel

theorem annihilate_four_create (Q : ℕ) (a x y z w : Fin (Q+1)) :
    annihilate a (create x (create y (create z (create w (1 : Space Q))))) =
      delta a x • create y (create z (create w (1 : Space Q))) -
      delta a y • create x (create z (create w (1 : Space Q))) +
      delta a z • create x (create y (create w (1 : Space Q))) -
      delta a w • create x (create y (create z (1 : Space Q))) := by
  rw [annihilate_create_apply,annihilate_three_create]
  simp only [map_sub,map_add,map_smul]
  abel

theorem pairEnd_four_create (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (x y z w : Fin (Q+1)) :
    pairEnd Q c (create x (create y (create z (create w (1 : Space Q))))) =
      (c x y-c y x) • create z (create w (1 : Space Q)) -
      (c x z-c z x) • create y (create w (1 : Space Q)) +
      (c x w-c w x) • create y (create z (1 : Space Q)) +
      (c y z-c z y) • create x (create w (1 : Space Q)) -
      (c y w-c w y) • create x (create z (1 : Space Q)) +
      (c z w-c w z) • create x (create y (1 : Space Q)) := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    annihilate_four_create,map_sub,map_add,map_smul,annihilate_three_create,
    smul_sub,smul_add,smul_smul,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp only [delta,mul_ite,mul_one,mul_zero,ite_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [sub_smul]
  abel

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
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_LimitCARReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairLimitCoefficient_swap (p x y : ℕ) :
    pairLimitCoefficient p y x = -pairLimitCoefficient p x y := by
  unfold pairLimitCoefficient
  rw [Nat.add_comm y x]
  split_ifs
  · rw [show ((2 : ℕ) : ℝ)^p * y.factorial*x.factorial =
      ((2 : ℕ) : ℝ)^p*x.factorial*y.factorial by ring]
    ring
  · simp

theorem pairLimitCoefficient_difference (p x y : ℕ) :
    pairLimitCoefficient p x y / Real.sqrt 2 - pairLimitCoefficient p y x / Real.sqrt 2 =
      Real.sqrt 2 * pairLimitCoefficient p x y := by
  rw [pairLimitCoefficient_swap p x y]
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc
    _ = 2 * pairLimitCoefficient p x y / Real.sqrt 2 := by ring
    _ = (Real.sqrt 2 * Real.sqrt 2) * pairLimitCoefficient p x y / Real.sqrt 2 := by rw [h]
    _ = _ := by field_simp

end Laughlin

namespace Laughlin.Fock
open scoped BigOperators

theorem limitPairEnd_four_create (Q p : ℕ) (a b c d : Fin (Q+1)) :
    limitPairEnd Q p (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt 2*pairLimitCoefficient p a.val b.val : ℝ) : ℂ) • create c (create d (1 : Space Q)) -
      ((Real.sqrt 2*pairLimitCoefficient p a.val c.val : ℝ) : ℂ) • create b (create d (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p a.val d.val : ℝ) : ℂ) • create b (create c (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p b.val c.val : ℝ) : ℂ) • create a (create d (1 : Space Q)) -
      ((Real.sqrt 2*pairLimitCoefficient p b.val d.val : ℝ) : ℂ) • create a (create c (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p c.val d.val : ℝ) : ℂ) • create a (create b (1 : Space Q)) := by
  unfold limitPairEnd
  rw [pairEnd_four_create]
  have he (x y : ℕ) : ((pairLimitCoefficient p x y / Real.sqrt 2 : ℝ) : ℂ) -
      ((pairLimitCoefficient p y x / Real.sqrt 2 : ℝ) : ℂ) =
      ((Real.sqrt 2 * pairLimitCoefficient p x y : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub,pairLimitCoefficient_difference]
  simp only [he]

theorem limitFourEnd_four_create (Q p : ℕ) (j k a b c d : Fin (Q+1)) :
    limitFourEnd Q p j k (create a (create b (create c (create d (1 : Space Q))))) =
      (((Real.sqrt 2*pairLimitCoefficient p a.val b.val : ℝ) : ℂ) * wedgeDelta Q j k c d -
       ((Real.sqrt 2*pairLimitCoefficient p a.val c.val : ℝ) : ℂ) * wedgeDelta Q j k b d +
       ((Real.sqrt 2*pairLimitCoefficient p a.val d.val : ℝ) : ℂ) * wedgeDelta Q j k b c +
       ((Real.sqrt 2*pairLimitCoefficient p b.val c.val : ℝ) : ℂ) * wedgeDelta Q j k a d -
       ((Real.sqrt 2*pairLimitCoefficient p b.val d.val : ℝ) : ℂ) * wedgeDelta Q j k a c +
       ((Real.sqrt 2*pairLimitCoefficient p c.val d.val : ℝ) : ℂ) * wedgeDelta Q j k a b) • (1 : Space Q) := by
  simp only [limitFourEnd,Module.End.mul_apply,limitPairEnd_four_create,map_sub,map_add,map_smul,
    two_annihilate_two_create,smul_smul,wedgeDelta,sub_smul,add_smul,smul_sub,mul_sub]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Parity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem physicalPairCoupling_antisymmetric (Q r j k : ℕ) (ho : Odd r) :
    physicalCouplingCoefficient Q Q r (j+k) k =
      -physicalCouplingCoefficient Q Q r (j+k) j := by
  by_cases h : r ≤ j+k ∧ j+k ≤ Q
  · have h1 : r ≤ j+k ∧ k ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q := by omega
    have h2 : r ≤ j+k ∧ j ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q := by omega
    rw [physicalCouplingCoefficient,dite_eq_left h1,physicalCouplingCoefficient,dite_eq_left h2]
    have hj : j+k-k=j := by omega
    have hk : j+k-j=k := by omega
    simp only [hj,hk]
    exact pairCoupledTensor_antisymmetric Q r (j+k-r) (by omega) ho
      ⟨j,by omega⟩ ⟨k,by omega⟩
  · have h1 : ¬(r ≤ j+k ∧ k ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q) := by omega
    have h2 : ¬(r ≤ j+k ∧ j ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q) := by omega
    simp only [physicalCouplingCoefficient,dite_eq_right h1,dite_eq_right h2,neg_zero]

theorem fourBodyCoefficient_antisymmetric (Q r D T p j k : ℕ) (ho : Odd r) :
    fourBodyCoefficient Q r D T p k j = -fourBodyCoefficient Q r D T p j k := by
  unfold fourBodyCoefficient
  rw [Nat.add_comm k j]
  by_cases hr : r ≤ j+k
  · rw [ite_eq_left hr,ite_eq_left hr,physicalPairCoupling_antisymmetric Q r j k ho]
    ring
  · rw [ite_eq_right hr,ite_eq_right hr,neg_zero]

theorem fourBodyLimitCoefficient_antisymmetric (r D T p j k : ℕ) (ho : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    fourBodyLimitCoefficient r D T p k j = -fourBodyLimitCoefficient r D T p j k := by
  apply tendsto_nhds_unique (source_fourBody_coefficient_tendsto r D T p k j hrD hDT (by omega))
  have h := (source_fourBody_coefficient_tendsto r D T p j k hrD hDT hT).neg
  apply h.congr
  intro Q
  exact (fourBodyCoefficient_antisymmetric Q r D T p j k ho).symm

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
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_SlaterRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem source_L_radical_cancellation (D r p x y j k : ℕ) (hor : Odd r)
    (hT : p+j+k=D) :
    Real.sqrt ((p.factorial : ℝ)/((2 : ℝ)^p*x.factorial*y.factorial)) * fourBodyRadical r D D p j k =
      Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
        (2 : ℝ)^(((1 : ℤ)-2*D+r)/2) *
        ((p.factorial : ℝ)*j.factorial*k.factorial) := by
  let e : ℤ := ((1 : ℤ)-2*D+r)/2
  have he : e*2=(1 : ℤ)-2*D+r := by
    rcases hor with ⟨a,ha⟩
    dsimp [e]; omega
  have hTr : (p : ℤ)+j+k=D := by exact_mod_cast hT
  have hpow : (2 : ℝ)^((1 : ℤ)-j-k-D+r) / (2 : ℝ)^p = ((2 : ℝ)^e)^2 := by
    rw [← zpow_natCast,← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (1 : ℤ)-j-k-D+r-(p : ℤ)=e*2 by omega,zpow_mul]
    norm_num
  have hsq : (Real.sqrt ((p.factorial : ℝ)/((2 : ℝ)^p*x.factorial*y.factorial)) *
      fourBodyRadical r D D p j k)^2 =
      (Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
        (2 : ℝ)^e * ((p.factorial : ℝ)*j.factorial*k.factorial))^2 := by
    simp only [fourBodyRadical,mul_pow]
    rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by unfold sourceCopyWeight; positivity)]
    simp only [Nat.sub_self,Nat.factorial_zero,Nat.cast_one,mul_one]
    calc
      _ = ((2 : ℝ)^((1 : ℤ)-j-k-D+r)/(2 : ℝ)^p) *
        (((p.factorial : ℝ)*j.factorial*k.factorial)^2 /
          ((r.factorial : ℝ)*(D-r).factorial*x.factorial*y.factorial*j.factorial*k.factorial)) := by
        field_simp
      _ = ((2 : ℝ)^e)^2 *
        (((p.factorial : ℝ)*j.factorial*k.factorial)^2 /
          ((r.factorial : ℝ)*(D-r).factorial*x.factorial*y.factorial*j.factorial*k.factorial)) := by rw [hpow]
      _ = _ := by unfold sourceCopyWeight; field_simp
  have hl : 0 ≤ Real.sqrt ((p.factorial : ℝ)/((2 : ℝ)^p*x.factorial*y.factorial)) *
      fourBodyRadical r D D p j k := by unfold fourBodyRadical; positivity
  have hr : 0 ≤ Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
      (2 : ℝ)^e * ((p.factorial : ℝ)*j.factorial*k.factorial) := by positivity
  nlinarith only [hsq,hl,hr]

theorem limitSlaterTerm_rational (D r x y j k : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hxy : x < y) (hT : x+y+j+k=D+1) :
    limitSlaterTerm D r x y j k =
      Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
        (2 : ℝ)^(((1 : ℤ)-2*D+r)/2) *
        ((x : ℝ)-y) * ((x+y-1).factorial : ℝ)*j.factorial*k.factorial *
        (Certificate.V r D D (x+y-1) j k : ℝ) := by
  have hp : x+y-1+j+k=D := by omega
  rw [limitSlaterTerm,source_fourBody_radical_coefficient r D D (x+y-1) j k hr (le_refl _) hp]
  rw [pairLimitCoefficient,ite_eq_left (by omega : x+y=x+y-1+1)]
  have hc := source_L_radical_cancellation D r (x+y-1) x y j k hor hp
  calc
    _ = ((x : ℝ)-y)*(Certificate.V r D D (x+y-1) j k : ℝ) *
      (Real.sqrt (((x+y-1).factorial : ℝ)/((2 : ℝ)^(x+y-1)*x.factorial*y.factorial)) *
        fourBodyRadical r D D (x+y-1) j k) := by
      simp only [Nat.cast_ofNat]
      field_simp
    _ = _ := by rw [hc]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_SlaterCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem source_fourBody_Slater_coefficient (D r a b c d : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hT : a+b+c+d=D+1) :
    limitSlaterCoefficient D r a b c d =
      Real.sqrt (sourceCopyWeight D r / ((a.factorial : ℝ)*b.factorial*c.factorial*d.factorial)) *
        (Certificate.L D r (a,b,c,d) : ℝ) := by
  unfold limitSlaterCoefficient
  rw [limitSlaterTerm_rational D r a b c d hr hor hab hT,
    limitSlaterTerm_rational D r a c b d hr hor (by omega) (by omega),
    limitSlaterTerm_rational D r a d b c hr hor (by omega) (by omega),
    limitSlaterTerm_rational D r b c a d hr hor hbc (by omega),
    limitSlaterTerm_rational D r b d a c hr hor (by omega) (by omega),
    limitSlaterTerm_rational D r c d a b hr hor hcd (by omega)]
  have h1 : (a.factorial : ℝ)*c.factorial*b.factorial*d.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h2 : (a.factorial : ℝ)*d.factorial*b.factorial*c.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h3 : (b.factorial : ℝ)*c.factorial*a.factorial*d.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h4 : (b.factorial : ℝ)*d.factorial*a.factorial*c.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h5 : (c.factorial : ℝ)*d.factorial*a.factorial*b.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  rw [h1,h2,h3,h4,h5]
  simp only [Certificate.L]
  push_cast
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_SliceCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem limitSliceCoefficient_antisymmetric (r D p j k : ℕ) (hr : r ≤ D) (ho : Odd r) :
    limitSliceCoefficient r D p k j = -limitSliceCoefficient r D p j k := by
  unfold limitSliceCoefficient
  by_cases h : p+j+k=D
  · rw [ite_eq_left (by omega : p+k+j=D),ite_eq_left h,
      fourBodyLimitCoefficient_antisymmetric r D D p j k ho hr (le_refl _) h]
  · rw [ite_eq_right (by omega : p+k+j ≠ D),ite_eq_right h,neg_zero]

theorem sum_pairLimit_slice (D r a b c d : ℕ) (hab : a < b) (hT : a+b+c+d=D+1) :
    (∑ p ∈ Finset.range (D+1), Real.sqrt 2 * pairLimitCoefficient p a b *
      limitSliceCoefficient r D p c d) = limitSlaterTerm D r a b c d := by
  rw [Finset.sum_eq_single (a+b-1)]
  · rw [limitSliceCoefficient,ite_eq_left (by omega)]
    rfl
  · intro p hp hne
    have h : a+b ≠ p+1 := by omega
    simp [pairLimitCoefficient,h]
  · intro h
    have hm : a+b-1 ∈ Finset.range (D+1) := Finset.mem_range.mpr (by omega)
    exact (h hm).elim

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_WeightedReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_weighted_wedgeDelta (Q : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
    (hS : ∀ j k, S k j = -S j k) (a b : Fin (Q+1)) :
    (∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ)*wedgeDelta Q j k a b) = (S a b : ℂ) := by
  simp only [wedgeDelta,delta,mul_sub,mul_ite,mul_one,mul_zero,
    Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [hS a b]
  push_cast
  ring

theorem sum_weighted_wedgeDelta_factor (Q : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
    (hS : ∀ j k, S k j = -S j k) (c : ℂ) (a b : Fin (Q+1)) :
    (∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ)*(c*wedgeDelta Q j k a b)) = c*(S a b : ℂ) := by
  calc
    _ = c*(∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ)*wedgeDelta Q j k a b) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro k hk; ring
    _ = _ := by rw [sum_weighted_wedgeDelta Q S hS a b]

theorem weightedFourEnd_readout (Q p : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
    (hS : ∀ j k, S k j = -S j k) (a b c d : Fin (Q+1)) :
    weightedFourEnd Q p S (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt 2*pairLimitCoefficient p a.val b.val*S c d -
        Real.sqrt 2*pairLimitCoefficient p a.val c.val*S b d +
        Real.sqrt 2*pairLimitCoefficient p a.val d.val*S b c +
        Real.sqrt 2*pairLimitCoefficient p b.val c.val*S a d -
        Real.sqrt 2*pairLimitCoefficient p b.val d.val*S a c +
        Real.sqrt 2*pairLimitCoefficient p c.val d.val*S a b : ℝ) : ℂ) • (1 : Space Q) := by
  simp only [weightedFourEnd,LinearMap.sum_apply,LinearMap.smul_apply,limitFourEnd_four_create,
    smul_smul,← Finset.sum_smul]
  congr 1
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    sum_weighted_wedgeDelta_factor Q S hS]
  push_cast
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_PhysicalSlaterReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem limitFourCopyEnd_Slater_readout (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hT : a.val+b.val+c.val+d.val=D+1) :
    limitFourCopyEnd Q r D (create a (create b (create c (create d (1 : Space Q))))) =
      (limitSlaterCoefficient D r a.val b.val c.val d.val : ℂ) • (1 : Space Q) := by
  simp only [limitFourCopyEnd,LinearMap.sum_apply]
  simp_rw [weightedFourEnd_readout Q _ _
    (fun j k => limitSliceCoefficient_antisymmetric r D _ j.val k.val hr hor)]
  rw [← Finset.sum_smul,← Complex.ofReal_sum]
  apply congrArg (fun v : ℝ => (v : ℂ) • (1 : Space Q))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [sum_pairLimit_slice D r a.val b.val c.val d.val hab hT,
    sum_pairLimit_slice D r a.val c.val b.val d.val (by exact_mod_cast lt_trans hab hbc) (by omega),
    sum_pairLimit_slice D r a.val d.val b.val c.val (by exact_mod_cast lt_trans hab (lt_trans hbc hcd)) (by omega),
    sum_pairLimit_slice D r b.val c.val a.val d.val hbc (by omega),
    sum_pairLimit_slice D r b.val d.val a.val c.val (by exact_mod_cast lt_trans hbc hcd) (by omega),
    sum_pairLimit_slice D r c.val d.val a.val b.val hcd (by omega)]
  rfl

theorem source_fourBody_physical_L_oai (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hT : a.val+b.val+c.val+d.val=D+1) :
    limitFourCopyEnd Q r D (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt (sourceCopyWeight D r /
        ((a.val.factorial : ℝ)*b.val.factorial*c.val.factorial*d.val.factorial)) *
        (Certificate.L D r (a.val,b.val,c.val,d.val) : ℝ) : ℝ) : ℂ) • (1 : Space Q) := by
  rw [limitFourCopyEnd_Slater_readout Q r D hr hor a b c d hab hbc hcd hT,
    source_fourBody_Slater_coefficient D r a.val b.val c.val d.val hr hor hab hbc hcd hT]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.source_fourBody_physical_L_oai := @OAI.Laughlin.Fock.source_fourBody_physical_L_oai
