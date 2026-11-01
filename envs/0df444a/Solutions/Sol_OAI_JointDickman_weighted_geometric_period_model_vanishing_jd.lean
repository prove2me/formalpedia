-- Prove2me | solution 1 for OAI.JointDickman.weighted_geometric_period_model_vanishing_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:22:16.335332+00:00
-- url     : https://prove2.me/submissions/46846266-183e-4f24-91ce-11cc7ae8ea66

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_coefficient_frozen_fullArc_integral_law_jd
import Theorems.Thm_OAI_JointDickman_largeMajorArc_box_bound_jd
import Theorems.Thm_OAI_JointDickman_squarefree_integer_rational_polylog_sum_bound_jd

section
-- module Solutions.OAIQ083_JD.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OscillatoryTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth oscillatory tests used in the coefficient estimate -/

namespace JointDickman

theorem norm_additivePhase (x : ℝ) : ‖additivePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_additivePhase (x : ℝ) :
    HasDerivAt additivePhase (additivePhase x * ((2 * Real.pi : ℝ) * Complex.I)) x := by
  have h := (((hasDerivAt_id x).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  simpa only [mul_one, id_eq] using! h

theorem continuous_additivePhase : Continuous additivePhase :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_additivePhase x).continuousAt)

theorem hasDerivAt_oscillatoryTest {w : ℝ → ℝ} {w' ξ t : ℝ}
    (hw : HasDerivAt w w' t) :
    HasDerivAt (oscillatoryTest w ξ) (oscillatoryTestDeriv w (fun _ => w') ξ t) t := by
  have hp := (hasDerivAt_additivePhase (ξ * t)).scomp t (hasDerivAt_const_mul ξ)
  simpa only [oscillatoryTest, oscillatoryTestDeriv, Function.comp_def, Complex.real_smul,
    mul_comm (ξ : ℂ)] using! hw.ofReal_comp.mul hp

theorem oscillatoryTest_norm (w : ℝ → ℝ) (ξ t : ℝ) :
    ‖oscillatoryTest w ξ t‖ = |w t| := by
  simp only [oscillatoryTest, norm_mul, norm_additivePhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

theorem oscillatoryTestDeriv_norm_le (w w' : ℝ → ℝ) (ξ t : ℝ) :
    ‖oscillatoryTestDeriv w w' ξ t‖ ≤ |w' t| + 2 * Real.pi * |ξ| * |w t| := by
  unfold oscillatoryTestDeriv
  calc
    _ ≤ ‖(w' t : ℂ) * additivePhase (ξ * t)‖ +
        ‖(w t : ℂ) * (additivePhase (ξ * t) * ((2 * Real.pi : ℝ) * Complex.I) * ξ)‖ :=
      norm_add_le _ _
    _ = _ := by
      simp only [norm_mul, norm_additivePhase, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one, one_mul, abs_of_pos Real.pi_pos, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem oscillatoryTestDeriv_continuousOn {w w' : ℝ → ℝ} {s : Set ℝ}
    (hw : ContinuousOn w s) (hw' : ContinuousOn w' s) (ξ : ℝ) :
    ContinuousOn (oscillatoryTestDeriv w w' ξ) s := by
  unfold oscillatoryTestDeriv
  have hp : ContinuousOn (fun t => additivePhase (ξ * t)) s :=
    (continuous_additivePhase.comp (continuous_const.mul continuous_id)).continuousOn
  exact ((Complex.continuous_ofReal.comp_continuousOn hw').mul hp).add
    ((Complex.continuous_ofReal.comp_continuousOn hw).mul ((hp.mul_const _).mul_const _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditivePhaseBridge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relating real exponential notation to residue characters -/

namespace JointDickman

theorem additivePhase_add (s t : ℝ) :
    additivePhase (s + t) = additivePhase s * additivePhase t := by
  unfold additivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteAdditiveOrthogonality
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite additive orthogonality for the arithmetic kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped ComplexConjugate

theorem additivePhase_conj (t : ℝ) : conj (additivePhase t) = additivePhase (-t) := by
  unfold additivePhase
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  ring

theorem integral_additivePhase_int (k : ℤ) :
    (∫ θ in (0 : ℝ)..1, additivePhase ((k : ℝ)*θ)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk,additivePhase]
  · have hc : (k : ℂ)*(2*(Real.pi : ℂ)*Complex.I) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hk)
        (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    have he : (fun θ : ℝ => additivePhase ((k : ℝ)*θ)) =
        (fun θ : ℝ => Complex.exp ((k : ℂ)*(2*(Real.pi : ℂ)*Complex.I)*θ)) := by
      funext θ
      unfold additivePhase
      congr 1
      push_cast
      ring
    rw [he,integral_exp_mul_complex hc]
    simp [hk,Complex.exp_int_mul_two_pi_mul_I]

theorem finiteAdditiveSum_continuous (s : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (finiteAdditiveSum s c) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_id))

theorem integral_additive_pair (n m : ℕ) (c d : ℂ) :
    (∫ θ in (0 : ℝ)..1,
      (c*additivePhase ((n : ℝ)*θ))*conj (d*additivePhase ((m : ℝ)*θ))) =
      if n = m then c*conj d else 0 := by
  have he : (fun θ : ℝ => (c*additivePhase ((n : ℝ)*θ))*
      conj (d*additivePhase ((m : ℝ)*θ))) =
      (fun θ : ℝ => (c*conj d)*additivePhase (((n : ℤ)-m : ℤ)*θ)) := by
    funext θ
    rw [map_mul,additivePhase_conj]
    have hp : additivePhase (((n : ℤ)-m : ℤ)*θ) =
        additivePhase ((n : ℝ)*θ)*additivePhase (-((m : ℝ)*θ)) := by
      rw [← additivePhase_add]
      congr 1
      push_cast
      ring
    rw [hp]
    ring
  rw [he,intervalIntegral.integral_const_mul,integral_additivePhase_int]
  by_cases h : n = m
  · simp [h]
  · have h' : (n : ℤ)-(m : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    simp [h,h']

/-- The exact finite Parseval pairing; different supports are allowed. -/
theorem finiteAdditiveSum_pair_integral (s t : Finset ℕ) (c d : ℕ → ℂ) :
    (∫ θ in (0 : ℝ)..1, finiteAdditiveSum s c θ*conj (finiteAdditiveSum t d θ)) =
      ∑ n ∈ s, ∑ m ∈ t, if n = m then c n*conj (d m) else 0 := by
  have hcont (n m : ℕ) : Continuous (fun θ : ℝ =>
      (c n*additivePhase ((n : ℝ)*θ))*conj (d m*additivePhase ((m : ℝ)*θ))) :=
    (continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_id))).mul
      (continuous_star.comp (continuous_const.mul
        (continuous_additivePhase.comp (continuous_const.mul continuous_id))))
  have hint (n m : ℕ) := (hcont n m).intervalIntegrable (μ := volume) 0 1
  simp only [finiteAdditiveSum,map_sum,mul_sum,sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [sum_comm]
    apply sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro m hm
      exact integral_additive_pair m n (c m) (d n)
    · intro m _
      exact hint m n
  · intro n _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro m _
    exact hcont m n

/-- Parseval for the finite trigonometric polynomials used in each box. -/
theorem finiteAdditiveSum_parseval (s : Finset ℕ) (c : ℕ → ℂ) :
    (∫ θ in (0 : ℝ)..1, ‖finiteAdditiveSum s c θ‖^2) = ∑ n ∈ s, ‖c n‖^2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (fun θ : ℝ => ((‖finiteAdditiveSum s c θ‖^2 : ℝ) : ℂ)) =
      (fun θ : ℝ => finiteAdditiveSum s c θ*conj (finiteAdditiveSum s c θ)) := by
    funext θ
    simp only [Complex.ofReal_pow,Complex.mul_conj']
  rw [he,finiteAdditiveSum_pair_integral]
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro n hn
  rw [sum_eq_single n]
  · simp [Complex.mul_conj']
  · intro m _ hmn
    simp [Ne.symm hmn]
  · exact fun h => (h hn).elim

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact removal of the small prime factors

Removing a finite set of prime factors is an exact convolution identity.
The moving roughness cutoff is then controlled by Selberg–Delange estimates.
-/

namespace JointDickman

open ArithmeticFunction Finset

theorem squarefreeWeight_isMultiplicative (z : ℝ) :
    (squarefreeWeight z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨squarefreeWeight_one z, fun {m n} hm hn hmn => ?_⟩
  simp only [squarefreeWeight, coe_mk, Nat.squarefree_mul hmn,
    ite_zero_mul_ite_zero, cardFactors_mul hm hn, pow_add]

theorem smoothCorrection_isMultiplicative (E : Finset ℕ) (z : ℝ) :
    (smoothCorrection E z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨smoothCorrection_one E z, fun {m n} hm hn _ => ?_⟩
  simp only [smoothCorrection, coe_mk, hm, hn, mul_ne_zero hm hn,
    ↓reduceIte, Nat.primeFactors_mul hm hn, union_subset_iff,
    cardFactors_mul hm hn, pow_add, ite_zero_mul_ite_zero]

theorem roughSquarefreeWeight_isMultiplicative (E : Finset ℕ) (z : ℝ) :
    (roughSquarefreeWeight E z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨roughSquarefreeWeight_one E z, fun {m n} hm hn hmn => ?_⟩
  simp only [roughSquarefreeWeight, coe_mk, Nat.primeFactors_mul hm hn,
    disjoint_union_left, (squarefreeWeight_isMultiplicative z).2 hmn,
    ite_zero_mul_ite_zero]

theorem squarefreeWeight_prime_pow (z : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    squarefreeWeight z (p ^ k) = if k = 1 then z else 0 := by
  by_cases hk1 : k = 1
  · simp [hk1, squarefreeWeight, hp.squarefree, cardFactors_apply_prime hp]
  · have hsq : ¬Squarefree (p ^ k) := by
      rw [Nat.squarefree_pow_iff hp.ne_one hk]
      simp [hk1]
    simp [squarefreeWeight, hsq, hk1]

theorem smoothCorrection_prime_pow (E : Finset ℕ) (z : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    smoothCorrection E z (p ^ k) = if p ∈ E then (-z) ^ k else 0 := by
  rw [smoothCorrection, coe_mk, ite_eq_right (pow_ne_zero k hp.ne_zero),
    Nat.primeFactors_pow p hk, hp.primeFactors]
  simp [cardFactors_apply_prime_pow hp]

theorem roughSquarefreeWeight_prime_pow (E : Finset ℕ) (z : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    roughSquarefreeWeight E z (p ^ k) =
      if p ∈ E then 0 else if k = 1 then z else 0 := by
  simp [roughSquarefreeWeight, Nat.primeFactors_pow p hk, hp.primeFactors,
    squarefreeWeight_prime_pow z hp hk]

/-- Only the divisors `1` and `p` contribute from the squarefree weight. -/
theorem squarefreeWeight_convolution_prime_pow (z : ℝ) (h : ArithmeticFunction ℝ)
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    (squarefreeWeight z * h) (p ^ k) = h (p ^ k) + z * h (p ^ (k - 1)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => squarefreeWeight z a * h b),
    Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ']
  simp only [pow_zero, squarefreeWeight_one, one_mul, Nat.div_one]
  have hpdiv : p ^ k / p = p ^ (k - 1) := by
    have hh := Nat.pow_div (m := k) (n := 1) (by omega : 1 ≤ k) hp.pos
    simpa only [pow_one] using hh
  simp_rw [squarefreeWeight_prime_pow z hp (Nat.succ_ne_zero _)]
  simp [hk, hpdiv, add_comm]

/-- Removing finitely many Euler factors is exact at every integer. -/
theorem squarefreeWeight_mul_smoothCorrection (E : Finset ℕ) (z : ℝ) :
    squarefreeWeight z * smoothCorrection E z = roughSquarefreeWeight E z := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((squarefreeWeight_isMultiplicative z).mul (smoothCorrection_isMultiplicative E z))
    _ (roughSquarefreeWeight_isMultiplicative E z)).mpr
  intro p k hp
  by_cases hk : k = 0
  · simp [hk]
  rw [squarefreeWeight_convolution_prime_pow z _ hp hk,
    smoothCorrection_prime_pow E z hp hk, roughSquarefreeWeight_prime_pow E z hp hk]
  by_cases hpE : p ∈ E
  · simp only [hpE, ite_eq_left]
    by_cases hk1 : k = 1
    · simp [hk1]
    · rw [smoothCorrection_prime_pow E z hp (by omega)]
      simp only [hpE, ite_eq_left]
      have hpow : k = (k - 1) + 1 := by omega
      nth_rw 1 [hpow]
      rw [pow_succ]
      ring
  · simp only [hpE, ↓reduceIte, zero_add]
    by_cases hk1 : k = 1
    · simp [hk1]
    · rw [smoothCorrection_prime_pow E z hp (by omega)]
      simp [hpE, hk1]

/-- Exact finite summatory identity used before the analytic truncation. -/
theorem roughSquarefreeWeight_summatory (E : Finset ℕ) (z : ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, roughSquarefreeWeight E z n) =
      ∑ v ∈ Ioc 0 N, smoothCorrection E z v *
        ∑ m ∈ Ioc 0 (N / v), squarefreeWeight z m := by
  rw [← squarefreeWeight_mul_smoothCorrection, mul_comm]
  exact sum_Ioc_mul_eq_sum_sum _ _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible parameters and elementary asymptotics

The strict inequalities here are the weight margins of `arithmetic.tex`.
The subsequent limits account for the sampling entropy and the logarithmic
factors in the prime cutoff and amplification parameters.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

/-- Every smaller real power is negligible compared with a larger one. -/
theorem power_div_power_tendsto_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun B : ℝ => B ^ a / B ^ b) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  rw [← Real.rpow_sub hB]
  congr 1
  ring

/-- In particular, each fixed polynomial degree below the cutoff exponent
is negligible compared with `P₀ = B^1000`. -/
theorem polynomial_div_primeCutoff_tendsto_zero {k : ℕ} (hk : k < 1000) :
    Tendsto (fun B : ℝ => B ^ k / B ^ (1000 : ℕ)) atTop (𝓝 0) := by
  have h : (k : ℝ) < (1000 : ℝ) := by exact_mod_cast hk
  have hlim := power_div_power_tendsto_zero h
  change Tendsto (fun B : ℝ => B ^ (k : ℝ) / B ^ ((1000 : ℕ) : ℝ))
    atTop (𝓝 0) at hlim
  simpa only [Real.rpow_natCast] using hlim

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal primes on fixed logarithmic intervals

Mertens' second theorem supplies the fixed-power interval limit. Together
with Chebyshev's estimate, it bounds the error in the marginal tuple count.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primesLE_eq_filter (N : ℕ) :
    Nat.primesLE N = (Icc 2 N).filter Nat.Prime := by
  apply Finset.ext
  intro p
  simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨⟨hp.two_le, hle⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨hle, hp⟩

theorem largePrimeSet_eq_sdiff {N y : ℝ} (hy : 0 ≤ y) :
    largePrimeSet N y = Nat.primesLE ⌊N⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
  apply Finset.ext
  intro p
  rw [Finset.mem_sdiff]
  simp only [largePrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpy⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    rintro ⟨hpy', _⟩
    exact (not_le_of_gt hpy) ((Nat.le_floor_iff hy).mp hpy')
  · rintro ⟨⟨hpN, hp⟩, hnot⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    by_contra h
    exact hnot ⟨Nat.le_floor (le_of_not_gt h), hp⟩

theorem largePrimeSet_reciprocal_eq {N y : ℝ} (hy : 0 ≤ y) (hyN : y ≤ N) :
    (∑ p ∈ largePrimeSet N y, 1 / (p : ℝ)) = primeReciprocalSum N - primeReciprocalSum y := by
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊N⌋₊ := by
    intro p hp
    obtain ⟨hpy, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpy.trans (Nat.floor_mono hyN), hp⟩
  rw [largePrimeSet_eq_sdiff hy]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSetWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite prime-selection and fair-split weights

The independent prime-set model and its fair splits satisfy exact finite
identities without prime asymptotics or analytic equidistribution premises.
-/

namespace JointDickman

open scoped BigOperators

theorem bernoulliSubsetMass_nonneg {α : Type*} [DecidableEq α]
    {P S : Finset α} {q : α → ℝ} (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    0 ≤ bernoulliSubsetMass P q S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun p hp => (hq p (hS hp)).1)
  · exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hq p
      (Finset.mem_sdiff.mp hp).1).2)

/-- Products of distinct prime sets remember their set of factors. -/
theorem primeProduct_injective {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P)
    (heq : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  have hSF := Nat.primeFactors_prod (fun p hp => hP p (hS hp))
  have hTF := Nat.primeFactors_prod (fun p hp => hP p (hT hp))
  rw [← hSF, ← hTF, heq]

theorem primeProductMass_at_product {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    primeProductMass P z (∏ p ∈ S, p) =
      bernoulliSubsetMass P (fun p => z / p) S := by
  classical
  unfold primeProductMass
  rw [Finset.sum_eq_single S]
  · simp
  · intro T hT hTS
    have hne : (∏ p ∈ T, p) ≠ ∏ p ∈ S, p :=
      fun heq => hTS (primeProduct_injective hP (Finset.mem_powerset.mp hT) hS heq)
    simp [hne]
  · intro hn
    exact False.elim (hn (Finset.mem_powerset.mpr hS))

theorem primeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    primeProductMass P z n = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq =>
    hn (Finset.mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProductComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparing finite product laws

Replacing one independent coordinate at a time bounds the `L¹` distance
of two finite product probability laws by the sum of their coordinate
distances. Applied to the mutually exclusive prime-site law, this gives
the accumulated quadratic error for arbitrary bounded complex tests.
All identities and inequalities here are proved by finite sums.
-/

namespace JointDickman

open scoped BigOperators

theorem bernoulliSubsetMass_eq_product {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S : P.powerset) :
    finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val)) (subsetHitEquiv P S) =
      bernoulliSubsetMass P q S.val := by
  classical
  have hp : finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val))
      (subsetHitEquiv P S) = ∏ i : P, if i.val ∈ S.val then q i.val else 1 - q i.val := by
    unfold finiteProductMass
    apply Finset.prod_congr rfl
    intro i _
    simp [bernoulliBitMass, subsetHitEquiv]
  rw [hp, show (∏ i : P, if i.val ∈ S.val then q i.val else 1 - q i.val) =
    ∏ i ∈ P, if i ∈ S.val then q i else 1 - q i from
      Finset.prod_coe_sort P (fun i => if i ∈ S.val then q i else 1 - q i), Finset.prod_ite]
  have hs : P.filter (fun i => i ∈ S.val) = S.val := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => Finset.mem_powerset.mp S.property hi)
  have hc : P.filter (fun i => i ∉ S.val) = P \ S.val := by
    ext i
    simp
  rw [hs, hc]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReciprocalTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative reciprocal-square tails

The error in the independent-product replacement is controlled by the tail
of all integers; no prime number theorem is needed here.
-/

namespace JointDickman

open Finset

theorem sum_reciprocal_square_tail (Q : Finset ℕ) {N : ℕ} (hN : N ≠ 0)
    (hQ : ∀ q ∈ Q, N < q) : (∑ q ∈ Q, 1 / (q : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  let M := max N (Q.sup id)
  have hsub : Q ⊆ Ioc N M := by
    intro q hq
    exact mem_Ioc.mpr ⟨hQ q hq, (le_sup (f := id) hq).trans (le_max_right _ _)⟩
  calc
    _ ≤ ∑ q ∈ Ioc N M, 1 / (q : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by
      simpa only [one_div] using (sum_Ioc_inv_sq_le_sub (α := ℝ) hN (le_max_left _ _))
    _ ≤ _ := sub_le_self _ (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogProductBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite logarithmic errors for prime-product normalizations

The quadratic logarithmic error is summable above the lower prime cutoff.
The inverse factors in the exact Bernoulli product mass are controlled
separately by a reciprocal sum over the selected primes.
-/

namespace JointDickman

open Finset

theorem log_one_sub_add_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  have hbase : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_of_nonneg hx, add_comm] using h
  have hden : 0 < 1 - x := by linarith
  apply hbase.trans
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem finite_log_product_error {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    |Real.log (∏ i ∈ P, (1 - x i)) + ∑ i ∈ P, x i| ≤ 2 * ∑ i ∈ P, (x i) ^ 2 := by
  rw [Real.log_prod (fun i hi => by linarith [(hx i hi).2]), ← sum_add_distrib]
  calc
    _ ≤ ∑ i ∈ P, |Real.log (1 - x i) + x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ P, 2 * (x i) ^ 2 := sum_le_sum fun i hi =>
      log_one_sub_add_error (hx i hi).1 (hx i hi).2
    _ = _ := (mul_sum _ _ _).symm

/-- A selected-prime normalizer differs logarithmically from the linear
reciprocal-prime sum by at most the reciprocal-square tail. -/
theorem prime_log_product_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ P, N < p) :
    |Real.log (∏ p ∈ P, (1 - z / (p : ℝ))) + z * ∑ p ∈ P, 1 / (p : ℝ)| ≤
      2 * z ^ 2 / (N : ℝ) := by
  have hx (p : ℕ) (hp : p ∈ P) : 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact ⟨div_nonneg hz hp0.le, (div_le_iff₀ hp0).mpr (by linarith)⟩
  have h := finite_log_product_error P (fun p => z / (p : ℝ)) hx
  have heq : (∑ p ∈ P, (z / (p : ℝ)) ^ 2) = z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    simp only [div_pow, mul_one_div]
  rw [heq] at h
  have hlin : (∑ p ∈ P, z / (p : ℝ)) = z * ∑ p ∈ P, 1 / (p : ℝ) := by
    simp only [mul_sum, mul_one_div]
  rw [hlin] at h
  calc
    _ ≤ 2 * (z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2) := h
    _ ≤ 2 * (z ^ 2 * (1 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut) (sq_nonneg z))
        (by norm_num)
    _ = _ := by ring

/-- The exact odds correction is bounded by an exponential of the
selected reciprocal mass, uniformly in the number of allowed primes. -/
theorem inverse_product_le_exp {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    (∏ i ∈ P, (1 - x i)⁻¹) ≤ Real.exp (2 * ∑ i ∈ P, x i) := by
  have hpoint (i : ι) (hi : i ∈ P) : (1 - x i)⁻¹ ≤ Real.exp (2 * x i) := by
    have hpos : 0 < 1 - x i := by linarith [(hx i hi).2]
    have herr := log_one_sub_add_error (hx i hi).1 (hx i hi).2
    have hlog : Real.log ((1 - x i)⁻¹) ≤ 2 * x i := by
      rw [Real.log_inv]
      have hmul := mul_nonneg (hx i hi).1 (show 0 ≤ 1 - 2 * x i by linarith [(hx i hi).2])
      nlinarith [(abs_le.mp herr).1]
    calc
      _ = Real.exp (Real.log ((1 - x i)⁻¹)) := (Real.exp_log (inv_pos.mpr hpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  calc
    _ ≤ ∏ i ∈ P, Real.exp (2 * x i) := Finset.prod_le_prod
      (fun i hi => inv_nonneg.mpr (by linarith [(hx i hi).2])) hpoint
    _ = Real.exp (∑ i ∈ P, 2 * x i) := (Real.exp_sum P (fun i => 2 * x i)).symm
    _ = _ := by rw [← mul_sum]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeNormalizer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the independent prime-product law

The logarithm of the all-absent probability is its linear prime sum up to
a reciprocal-square error. Mertens' second theorem therefore determines
the normalization for a moving lower and upper cutoff.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- Both endpoint Mertens remainders control the prime-interval remainder. -/
theorem prime_interval_mertens_error
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : ℝ, 2 ≤ X → X ≤ Y →
      |(∑ p ∈ largePrimeSet Y X, 1 / (p : ℝ)) -
        (Real.log (Real.log Y) - Real.log (Real.log X))| ≤
        C / Real.log Y + C / Real.log X := by
  obtain ⟨M, C, hC, hbound⟩ := hM
  refine ⟨C, hC, fun X Y hX hXY => ?_⟩
  have hY : 2 ≤ Y := hX.trans hXY
  have h₁ : |primeReciprocalSum X - Real.log (Real.log X) - M| ≤ C / Real.log X := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound X hX
  have h₂ : |primeReciprocalSum Y - Real.log (Real.log Y) - M| ≤ C / Real.log Y := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound Y hY
  rw [largePrimeSet_reciprocal_eq (by linarith) hXY]
  calc
    _ = |(primeReciprocalSum Y - Real.log (Real.log Y) - M) -
        (primeReciprocalSum X - Real.log (Real.log X) - M)| := by congr 1; ring
    _ ≤ |primeReciprocalSum Y - Real.log (Real.log Y) - M| +
        |primeReciprocalSum X - Real.log (Real.log X) - M| := abs_sub _ _
    _ ≤ _ := add_le_add h₂ h₁

/-- Uniform logarithmic normalizer error, retaining both endpoint errors. -/
theorem primeNormalizer_log_error
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (Y z : ℝ), 2 ≤ N → (N : ℝ) ≤ Y →
      0 ≤ z → z ≤ 1 →
      |Real.log (primeNormalizer (largePrimeSet Y N) z) +
        z * Real.log (Real.log Y / Real.log N)| ≤
        2 * z ^ 2 / (N : ℝ) + z * (C / Real.log Y + C / Real.log N) := by
  obtain ⟨C, hC, hinterval⟩ := prime_interval_mertens_error hM
  refine ⟨C, hC, fun N Y z hN hNY hz hz1 => ?_⟩
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hP : ∀ p ∈ largePrimeSet Y (N : ℝ), p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hcut : ∀ p ∈ largePrimeSet Y (N : ℝ), N < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have h₁ := prime_log_product_error (largePrimeSet Y N) hP hz hz1
    (show N ≠ 0 by omega) hcut
  have h₂ := hinterval (N : ℝ) Y hNreal hNY
  have hlog : Real.log (Real.log Y / Real.log N) =
      Real.log (Real.log Y) - Real.log (Real.log N) :=
    Real.log_div hlogY.ne' hlogN.ne'
  let S := ∑ p ∈ largePrimeSet Y (N : ℝ), 1 / (p : ℝ)
  change |Real.log (primeNormalizer (largePrimeSet Y N) z) + z * Real.log (Real.log Y / Real.log N)| ≤ _
  calc
    _ = |(Real.log (primeNormalizer (largePrimeSet Y N) z) + z * S) +
        z * (Real.log (Real.log Y / Real.log N) - S)| := by congr 1; ring
    _ ≤ |Real.log (primeNormalizer (largePrimeSet Y N) z) + z * S| +
        |z * (Real.log (Real.log Y / Real.log N) - S)| := abs_add_le _ _
    _ ≤ 2 * z ^ 2 / (N : ℝ) + z * (C / Real.log Y + C / Real.log N) := by
      apply add_le_add h₁
      rw [abs_mul, abs_of_nonneg hz, abs_sub_comm, hlog]
      exact mul_le_mul_of_nonneg_left h₂ hz

/-- The all-absent product has the expected logarithmic normalization.
Only Mertens' reciprocal-prime input is used. -/
theorem primeNormalizer_normalized_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (N : ℕ → ℕ) (Y : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (hY : Tendsto Y atTop atTop) (hNY : ∀ᶠ B in atTop, (N B : ℝ) ≤ Y B)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => primeNormalizer (largePrimeSet (Y B) (N B)) z *
      (Real.log (Y B) / Real.log (N B)) ^ z) atTop (𝓝 1) := by
  obtain ⟨C, _, hbound⟩ := primeNormalizer_log_error hM
  have hNreal : Tendsto (fun B => (N B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hlim : Tendsto (fun B => 2 * z ^ 2 / (N B : ℝ) +
      z * (C / Real.log (Y B) + C / Real.log (N B))) atTop (𝓝 0) := by
    have h₁ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * z ^ 2) atTop (𝓝 (2 * z ^ 2))).div_atTop hNreal
    have h₂ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).div_atTop
      (Real.tendsto_log_atTop.comp hY)
    have h₃ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).div_atTop
      (Real.tendsto_log_atTop.comp hNreal)
    simpa using h₁.add ((h₂.add h₃).const_mul z)
  let E := fun B => Real.log (primeNormalizer (largePrimeSet (Y B) (N B)) z) +
    z * Real.log (Real.log (Y B) / Real.log (N B))
  have hE : Tendsto E atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    filter_upwards [hN.eventually (eventually_ge_atTop 2), hNY] with B hNB hNYB
    simpa [E, Real.norm_eq_abs] using hbound (N B) (Y B) z hNB hNYB hz hz1
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hE
  have heq : (fun B => Real.exp (E B)) =ᶠ[atTop]
      (fun B => primeNormalizer (largePrimeSet (Y B) (N B)) z *
        (Real.log (Y B) / Real.log (N B)) ^ z) := by
    filter_upwards [hN.eventually (eventually_ge_atTop 2), hNY] with B hNB hNYB
    have hN2 : (2 : ℝ) ≤ N B := by exact_mod_cast hNB
    have hlogN : 0 < Real.log (N B) := Real.log_pos (by linarith)
    have hlogY : 0 < Real.log (Y B) := Real.log_pos (by linarith)
    have hprod : 0 < primeNormalizer (largePrimeSet (Y B) (N B)) z := by
      apply prod_pos
      intro p hp
      have hprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hfrac : z / (p : ℝ) < 1 := (div_lt_one hp0).mpr (by linarith)
      linarith
    dsimp [E]
    rw [Real.exp_add, Real.exp_log hprod,
      Real.rpow_def_of_pos (div_pos hlogY hlogN)]
    congr 1
    congr 1
    ring
  simpa using hexp.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughErrorLimits
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Decay of the roughness-cutoff errors

The exponential Rankin error absorbs every fixed power of the scale
and of its logarithm. This is the limit needed after the explicit
moving-cutoff expansion.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

theorem rough_exponential_error_tendsto {a K C : ℝ}
    (ha : 0 < a) (hK : 0 < K) (hC : 0 ≤ C) (D : ℝ) :
    Tendsto (fun B : ℝ => B ^ D * (Real.log B) ^ C *
      Real.exp (-(B ^ a / (K * Real.log B)))) atTop (𝓝 0) := by
  have ha2 : 0 < a / 2 := by positivity
  have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((D + C) / (a / 2)) (1 / K) (by positivity)).comp (tendsto_rpow_atTop ha2)
  have hlim : Tendsto (fun B : ℝ => B ^ (D + C) *
      Real.exp (-(1 / K) * B ^ (a / 2))) atTop (𝓝 0) := by
    apply hbase.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    dsimp
    rw [← Real.rpow_mul hB.le]
    congr 2
    field_simp
  have hsmall := (isLittleO_log_rpow_atTop ha2).def (by norm_num : (0 : ℝ) < 1)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Real.log_pos hB).le _))
      (Real.exp_pos _).le
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hsmall] with B hB hs
    have hB0 : 0 < B := by linarith
    have hlog : 0 < Real.log B := Real.log_pos hB
    have hlogpow : Real.log B ≤ B ^ (a / 2) := by
      simpa only [Real.norm_eq_abs, abs_of_pos hlog,
        abs_of_pos (Real.rpow_pos_of_pos hB0 _), one_mul] using hs
    have hlogB : Real.log B ≤ B := by linarith [Real.log_le_sub_one_of_pos hB0]
    have hlogC : (Real.log B) ^ C ≤ B ^ C :=
      Real.rpow_le_rpow hlog.le hlogB hC
    have hden : K * Real.log B ≤ K * B ^ (a / 2) :=
      mul_le_mul_of_nonneg_left hlogpow hK.le
    have hquot : (1 / K) * B ^ (a / 2) ≤ B ^ a / (K * Real.log B) := by
      calc
        _ = B ^ a / (K * B ^ (a / 2)) := by
          have hsquare : B ^ a = B ^ (a / 2) * B ^ (a / 2) := by
            rw [← Real.rpow_add hB0]
            congr 1
            ring
          rw [hsquare]
          field_simp
        _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hB0.le _)
          (mul_pos hK hlog) hden
    have hexp : Real.exp (-(B ^ a / (K * Real.log B))) ≤
        Real.exp (-(1 / K) * B ^ (a / 2)) := by
      apply Real.exp_le_exp.mpr
      linarith
    calc
      _ ≤ (B ^ D * B ^ C) * Real.exp (-(1 / K) * B ^ (a / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlogC (Real.rpow_nonneg hB0.le _))
          hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [← Real.rpow_add hB0]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The manuscript's auxiliary prime scale

The lower cutoff is `B^1000`, the upper cutoff is `exp (4 B)`, and
`R = B / log (B^1000)`. The normalizing constant below is derived from
the published reciprocal-prime Mertens estimate.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

theorem auxiliaryCutoff_tendsto : Tendsto auxiliaryCutoff atTop atTop :=
  tendsto_pow_atTop (by norm_num : (1000 : ℕ) ≠ 0)

theorem auxiliaryUpper_tendsto : Tendsto auxiliaryUpper atTop atTop :=
  Real.tendsto_exp_atTop.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4))

theorem auxiliaryCutoff_le_upper :
    ∀ᶠ B in atTop, (auxiliaryCutoff B : ℝ) ≤ auxiliaryUpper B := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 1000 (by norm_num : (0 : ℝ) < 4)).def
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with B hB
  have hpow : (0 : ℝ) ≤ (B : ℝ) ^ 1000 := pow_nonneg (Nat.cast_nonneg B) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hpow,
    abs_of_pos (Real.exp_pos _), one_mul, auxiliaryCutoff, auxiliaryUpper,
    Nat.cast_pow] using hB

theorem auxiliaryRatio_pos {B : ℕ} (hB : 1 < B) : 0 < auxiliaryRatio B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  exact div_pos (by linarith) (mul_pos (by norm_num) (Real.log_pos hBreal))

theorem auxiliaryRatio_tendsto : Tendsto auxiliaryRatio atTop atTop := by
  have hlim : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ)))
      atTop (𝓝 0) := by
    simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul 1000
  have hpos : ∀ᶠ B : ℕ in atTop, 0 < 1000 * (Real.log B / (B : ℝ)) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
    exact mul_pos (by norm_num) (div_pos (Real.log_pos hBreal) (by linarith))
  have hgt : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ)))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hlim, hpos⟩
  convert hgt.inv_tendsto_nhdsGT_zero using 1
  all_goals try with_reducible_and_instances rfl
  ext B
  simp only [auxiliaryRatio, Pi.inv_apply, mul_inv_rev, inv_div]
  ring

theorem auxiliary_log_ratio (B : ℕ) :
    Real.log (auxiliaryUpper B) / Real.log (auxiliaryCutoff B) =
      4 * auxiliaryRatio B := by
  simp only [auxiliaryUpper, Real.log_exp, auxiliaryCutoff, Nat.cast_pow,
    Real.log_pow, auxiliaryRatio]
  ring

/-- The paper's `Q_{z,B} ~ (4 R)^{-z}` in normalized-limit form. -/
theorem auxiliary_primeNormalizer_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => primeNormalizer (auxiliaryPrimes B) z *
      auxiliaryRatio B ^ z) atTop (𝓝 ((4 : ℝ) ^ (-z))) := by
  have h := primeNormalizer_normalized_tendsto hM auxiliaryCutoff auxiliaryUpper
    auxiliaryCutoff_tendsto auxiliaryUpper_tendsto auxiliaryCutoff_le_upper hz hz1
  simp_rw [auxiliary_log_ratio] at h
  have hdiv := h.div_const ((4 : ℝ) ^ z)
  have heq : (fun B => primeNormalizer (largePrimeSet (auxiliaryUpper B)
      (auxiliaryCutoff B)) z * (4 * auxiliaryRatio B) ^ z / (4 : ℝ) ^ z)
      =ᶠ[atTop] (fun B => primeNormalizer (auxiliaryPrimes B) z * auxiliaryRatio B ^ z) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (auxiliaryRatio_pos hB).le]
    change _ = primeNormalizer (largePrimeSet (auxiliaryUpper B) (auxiliaryCutoff B)) z * _
    have hfour : (4 : ℝ) ^ z ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) z).ne'
    field_simp
  simpa [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)] using hdiv.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ConvolutionTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite truncation estimates for roughness removal

The large-divisor part of the convolution is bounded before invoking any
Selberg–Delange input. The bound needs only the elementary `|g_z| ≤ 1`.
-/

namespace JointDickman

open Finset

theorem squarefreeWeight_abs_le_one {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    |squarefreeWeight z n| ≤ 1 := by
  unfold squarefreeWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs
  · rw [abs_of_nonneg (pow_nonneg hz _)]
    exact pow_le_one₀ hz hz1
  · norm_num

theorem squarefreeWeight_sum_abs_le {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (N : ℕ) :
    |∑ n ∈ Ioc 0 N, squarefreeWeight z n| ≤ N := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, |squarefreeWeight z n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℝ) := sum_le_sum fun n _ => squarefreeWeight_abs_le_one hz hz1 n
    _ = _ := by simp

theorem roughConvolutionTail_abs_le (E : Finset ℕ) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (N V : ℕ) :
    |roughConvolutionTail E z N V| ≤
      (N : ℝ) * ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) := by
  unfold roughConvolutionTail
  calc
    _ ≤ ∑ v ∈ Ioc V N, |smoothCorrection E z v *
        ∑ m ∈ Ioc 0 (N / v), squarefreeWeight z m| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ Ioc V N, (N : ℝ) * (|smoothCorrection E z v| / v) := by
      apply sum_le_sum
      intro v hv
      have hvpos : 0 < v := (mem_Ioc.mp hv).1.trans_le' (Nat.zero_le V)
      have hvpos' : (0 : ℝ) < v := by exact_mod_cast hvpos
      have hfloor : ((N / v : ℕ) : ℝ) ≤ (N : ℝ) / v := by
        apply (le_div_iff₀ hvpos').mpr
        exact_mod_cast Nat.div_mul_le_self N v
      rw [abs_mul]
      calc
        _ ≤ |smoothCorrection E z v| * ((N / v : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (squarefreeWeight_sum_abs_le hz hz1 _) (abs_nonneg _)
        _ ≤ |smoothCorrection E z v| * ((N : ℝ) / v) :=
          mul_le_mul_of_nonneg_left hfloor (abs_nonneg _)
        _ = _ := by ring
    _ = _ := (mul_sum _ _ _).symm

/-- The elementary Rankin inequality for the harmonic tail. -/
theorem harmonic_tail_rankin {ι : Type*} (s : Finset ι) (v a : ι → ℝ)
    {V ε : ℝ} (hV : 0 < V) (hε : 0 ≤ ε)
    (hv : ∀ i ∈ s, V ≤ v i) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i / v i) ≤
      (∑ i ∈ s, a i / (v i) ^ (1 - ε)) / V ^ ε := by
  have hVpow : 0 < V ^ ε := Real.rpow_pos_of_pos hV _
  apply (le_div_iff₀ hVpow).mpr
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  have hvi : 0 < v i := hV.trans_le (hv i hi)
  have hpow : V ^ ε ≤ (v i) ^ ε := Real.rpow_le_rpow hV.le (hv i hi) hε
  calc
    a i / v i * V ^ ε ≤ a i / v i * (v i) ^ ε :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg (ha i hi) hvi.le)
    _ = a i / (v i) ^ (1 - ε) := by
      rw [Real.rpow_sub hvi, Real.rpow_one]
      field_simp

/-- Quantitative large-divisor truncation in terms of one weighted moment
of the correction coefficients. -/
theorem roughConvolutionTail_rankin (E : Finset ℕ) {z ε : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 ≤ ε) (N V : ℕ) (hV : 0 < V) :
    |roughConvolutionTail E z N V| ≤
      ((N : ℝ) / (V : ℝ) ^ ε) *
        ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) ^ (1 - ε) := by
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have h := harmonic_tail_rankin (Ioc V N) (fun v : ℕ => (v : ℝ))
    (fun v => |smoothCorrection E z v|) hV' hε
    (fun v hv => by exact_mod_cast (mem_Ioc.mp hv).1.le)
    (fun _ _ => abs_nonneg _)
  calc
    _ ≤ (N : ℝ) * ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) :=
      roughConvolutionTail_abs_le E hz hz1 N V
    _ ≤ (N : ℝ) * ((∑ v ∈ Ioc V N, |smoothCorrection E z v| /
        (v : ℝ) ^ (1 - ε)) / (V : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothCorrectionSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The convergent correction series

The finite Euler factors used in removing the small primes are proved
as identities of absolutely convergent series, including at the shifted
exponent required by Rankin's bound.
-/

namespace JointDickman

open Finset

theorem smoothDirichletTerm_mul (E : Finset ℕ) (z s : ℝ) {m n : ℕ}
    (hmn : m.Coprime n) :
    smoothDirichletTerm E z s (m * n) =
      smoothDirichletTerm E z s m * smoothDirichletTerm E z s n := by
  simp only [smoothDirichletTerm, (smoothCorrection_isMultiplicative E z).map_mul_of_coprime hmn,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

theorem smoothDirichletTerm_prime_pow (E : Finset ℕ) (z s : ℝ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    smoothDirichletTerm E z s (p ^ k) =
      (if p ∈ E then -z / (p : ℝ) ^ s else 0) ^ k := by
  by_cases hk : k = 0
  · simp [hk]
  simp only [smoothDirichletTerm, smoothCorrection_prime_pow E z hp hk, Nat.cast_pow,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (k : ℝ) s,
    Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  split_ifs <;> simp [div_pow, hk]

theorem smoothDirichletTerm_ratio_lt_one (E : Finset ℕ) {z s : ℝ}
    (hz : |z| < 1) (hs : 0 ≤ s) {p : ℕ} (hp : p.Prime) :
    ‖(if p ∈ E then -z / (p : ℝ) ^ s else 0)‖ < 1 := by
  by_cases hpE : p ∈ E
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpow : (1 : ℝ) ≤ (p : ℝ) ^ s := Real.one_le_rpow hp1 hs
    simp only [hpE, ite_eq_left, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (Real.rpow_pos_of_pos hp0 s)]
    exact (div_lt_one (Real.rpow_pos_of_pos hp0 s)).mpr (hz.trans_le hpow)
  · simp [hpE]

theorem smoothDirichletTerm_support (E : Finset ℕ) (z s : ℝ) :
    Function.support (smoothDirichletTerm E z s) ⊆ Nat.factoredNumbers E := by
  intro n hn
  rw [Function.mem_support] at hn
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp [smoothDirichletTerm] at hn
  refine ⟨hn0, ?_⟩
  by_contra h
  simp [smoothDirichletTerm, smoothCorrection, hn0, h] at hn

/-- Absolute convergence and the signed Euler-factor identity. -/
theorem smoothCorrection_hasSum (E : Finset ℕ) {z s : ℝ}
    (hz : |z| < 1) (hs : 0 ≤ s) :
    Summable (fun n => ‖smoothDirichletTerm E z s n‖) ∧
      HasSum (smoothDirichletTerm E z s)
        (∏ p ∈ E with p.Prime, (1 + z / (p : ℝ) ^ s)⁻¹) := by
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k => ‖smoothDirichletTerm E z s (p ^ k)‖) := by
    intro p hp
    simp_rw [smoothDirichletTerm_prime_pow E z s hp]
    exact summable_norm_geometric_of_norm_lt_one
      (smoothDirichletTerm_ratio_lt_one E hz hs hp)
  obtain ⟨hnorm, hsum⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      (smoothDirichletTerm_one E z s) (smoothDirichletTerm_mul E z s) hlocal E
  have hsupport := smoothDirichletTerm_support E z s
  have habs_support : Function.support (fun n => ‖smoothDirichletTerm E z s n‖) ⊆
      Nat.factoredNumbers E := by
    intro n hn
    apply hsupport
    simpa only [Function.mem_support, norm_ne_zero_iff] using hn
  refine ⟨((hasSum_subtype_iff_of_support_subset habs_support).mp hnorm.hasSum).summable, ?_⟩
  apply (hasSum_subtype_iff_of_support_subset hsupport).mp
  convert hsum using 1
  all_goals try rfl
  apply prod_congr rfl
  intro p hp
  obtain ⟨_, hprime⟩ := mem_filter.mp hp
  simp_rw [smoothDirichletTerm_prime_pow E z s hprime]
  rw [(hasSum_geometric_of_norm_lt_one
    (smoothDirichletTerm_ratio_lt_one E hz hs hprime)).tsum_eq]
  simp [mem_of_mem_filter p hp, sub_eq_add_neg, neg_div]

/-- The zeroth correction moment is the inverse of the removed local factors. -/
theorem smoothCorrection_zeroth_moment (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    HasSum (fun n => smoothCorrection E z n / (n : ℝ))
      (∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹) := by
  have h := (smoothCorrection_hasSum E hz (by norm_num : (0 : ℝ) ≤ 1)).2
  have hf : smoothDirichletTerm E z 1 = fun n => smoothCorrection E z n / (n : ℝ) := by
    funext n
    simp [smoothDirichletTerm]
  rw [hf] at h
  simpa using h

theorem smoothDirichletTerm_abs (E : Finset ℕ) {z : ℝ} (hz : 0 ≤ z)
    (s : ℝ) (n : ℕ) :
    |smoothDirichletTerm E z s n| = smoothDirichletTerm E (-z) s n := by
  simp only [smoothDirichletTerm, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s),
    smoothCorrection, ArithmeticFunction.coe_mk]
  split_ifs <;> simp [abs_pow, abs_neg, abs_of_nonneg hz]

/-- The absolute correction moment is a finite product of positive geometric factors. -/
theorem smoothCorrection_abs_hasSum (E : Finset ℕ) {z s : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hs : 0 ≤ s) :
    HasSum (fun n => |smoothCorrection E z n| / (n : ℝ) ^ s)
      (∏ p ∈ E with p.Prime, (1 - z / (p : ℝ) ^ s)⁻¹) := by
  have hz' : |-z| < 1 := by simpa [abs_of_nonneg hz] using hz1
  have h := (smoothCorrection_hasSum E hz' hs).2
  have hf : smoothDirichletTerm E (-z) s =
      fun n => |smoothCorrection E z n| / (n : ℝ) ^ s := by
    funext n
    rw [← smoothDirichletTerm_abs E hz]
    simp [smoothDirichletTerm, abs_div,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
  rw [hf] at h
  simpa [neg_div, sub_eq_add_neg] using h

/-- An exponential bound for every finite truncation of the absolute series. -/
theorem smoothCorrection_abs_sum_le_exp (E S : Finset ℕ) {z s : ℝ}
    (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (hs : 0 ≤ s) :
    (∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) ^ s) ≤
      Real.exp (2 * z * ∑ p ∈ E with p.Prime, 1 / (p : ℝ) ^ s) := by
  have hsum := smoothCorrection_abs_hasSum E hz (by linarith) hs
  calc
    _ ≤ ∏ p ∈ E with p.Prime, (1 - z / (p : ℝ) ^ s)⁻¹ := by
      rw [← hsum.tsum_eq]
      exact hsum.summable.sum_le_tsum S (fun n _ =>
        div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) s))
    _ ≤ Real.exp (2 * ∑ p ∈ E with p.Prime, z / (p : ℝ) ^ s) := by
      apply inverse_product_le_exp
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.one_lt.le
      have hpow := Real.one_le_rpow hp1 hs
      refine ⟨div_nonneg hz (by positivity), ?_⟩
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    _ = _ := by
      congr 1
      simp only [div_eq_mul_inv, one_mul, ← mul_sum]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMomentBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds for the moving roughness correction

The exponent shift `1 / log P` costs only a fixed power of `log P`.
This supplies the moment in Rankin's argument from Mertens' estimate,
rather than assuming a cutoff-dependent bound.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem shifted_reciprocal_le {p P : ℝ} (hp : 0 < p) (hpP : p ≤ P)
    (hlog : 0 < Real.log P) :
    1 / p ^ (1 - 1 / Real.log P) ≤ Real.exp 1 / p := by
  have hpow : p ^ (1 / Real.log P) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hp]
    apply Real.exp_le_exp.mpr
    have hle : Real.log p ≤ Real.log P := Real.log_le_log hp hpP
    simpa only [mul_one_div] using (div_le_one hlog).mpr hle
  rw [Real.rpow_sub hp, Real.rpow_one]
  simpa only [one_div_div] using div_le_div_of_nonneg_right hpow hp.le

theorem shifted_prime_sum_le (P : ℕ) (hlog : 0 < Real.log P) :
    (∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P)) ≤
      Real.exp 1 * primeReciprocalSum P := by
  simp only [primeReciprocalSum, Nat.floor_natCast, mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpP, hprime⟩ := Nat.mem_primesLE.mp hp
  simpa only [mul_one_div] using shifted_reciprocal_le
    (by exact_mod_cast hprime.pos) (by exact_mod_cast hpP) hlog

/-- Mertens controls the shifted absolute correction moment by a fixed
power of the logarithm, uniformly over all finite truncations. -/
theorem smoothCorrection_shifted_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (S : Finset ℕ) (z : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      (∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| /
        (n : ℝ) ^ (1 - 1 / Real.log P)) ≤
        A * (Real.log P) ^ (Real.exp 1) := by
  obtain ⟨M, C, hC, hbound⟩ := hM
  refine ⟨Real.exp (Real.exp 1 * (|M| + C)), Real.exp_pos _, ?_⟩
  intro P S z hP hlog hz hzhalf
  have hlogpos : 0 < Real.log P := by linarith
  have hshift : 0 ≤ 1 - 1 / Real.log P := by
    have h := (div_le_one hlogpos).mpr hlog
    linarith
  have hMertens : primeReciprocalSum P ≤ Real.log (Real.log P) + |M| + C := by
    have h := (abs_le.mp (hbound P (by exact_mod_cast hP))).2
    have hCdiv : C / Real.log P ≤ C := (div_le_iff₀ hlogpos).mpr (by nlinarith)
    have hMabs := le_abs_self M
    simp only [← primesLE_eq_filter] at h
    change primeReciprocalSum P - Real.log (Real.log P) - M ≤ C / Real.log P at h
    linarith
  have hprime : (Nat.primesLE P).filter Nat.Prime = Nat.primesLE P :=
    filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  calc
    _ ≤ Real.exp (2 * z * ∑ p ∈ Nat.primesLE P,
        1 / (p : ℝ) ^ (1 - 1 / Real.log P)) := by
      simpa only [hprime] using smoothCorrection_abs_sum_le_exp
        (Nat.primesLE P) S hz hzhalf hshift
    _ ≤ Real.exp (∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P)) := by
      apply Real.exp_le_exp.mpr
      have hsum : 0 ≤ ∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P) :=
        sum_nonneg (fun p _ => by positivity)
      nlinarith
    _ ≤ Real.exp (Real.exp 1 * primeReciprocalSum P) :=
      Real.exp_le_exp.mpr (shifted_prime_sum_le P hlogpos)
    _ ≤ Real.exp (Real.exp 1 * (Real.log (Real.log P) + |M| + C)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hMertens (Real.exp_pos _).le)
    _ = _ := by
      rw [show Real.exp 1 * (Real.log (Real.log P) + |M| + C) =
        Real.exp 1 * (|M| + C) + Real.log (Real.log P) * Real.exp 1 by ring,
        Real.exp_add, ← Real.rpow_def_of_pos hlogpos]

/-- The same constant controls the actual large-divisor convolution error. -/
theorem roughConvolutionTail_shifted_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P N V : ℕ) (z : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 0 < V → 0 ≤ z → z ≤ 1 / 2 →
      |roughConvolutionTail (Nat.primesLE P) z N V| ≤
        (N : ℝ) / (V : ℝ) ^ (1 / Real.log P) *
          (A * (Real.log P) ^ (Real.exp 1)) := by
  obtain ⟨A, hA, hmoment⟩ := smoothCorrection_shifted_bound hM
  refine ⟨A, hA, fun P N V z hP hlog hV hz hzhalf => ?_⟩
  have hlogpos : 0 < Real.log P := by linarith
  exact (roughConvolutionTail_rankin (Nat.primesLE P) hz (by linarith)
    (by positivity) N V hV).trans
      (mul_le_mul_of_nonneg_left (hmoment P (Ioc V N) z hP hlog hz hzhalf)
        (by positivity))

theorem log_pow_le_rpow (k : ℕ) {v ε : ℝ} (hv : 1 ≤ v) (hε : 0 < ε) :
    (Real.log v) ^ k ≤ ((k.factorial : ℝ) / ε ^ k) * v ^ ε := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h := (div_le_iff₀ hfact).mp
    (Real.pow_div_factorial_le_exp (ε * Real.log v) (mul_nonneg hε.le (Real.log_nonneg hv)) k)
  have hexp : Real.exp (ε * Real.log v) = v ^ ε := by
    rw [Real.rpow_def_of_pos hv0, mul_comm]
  rw [mul_pow, hexp] at h
  calc
    (Real.log v) ^ k ≤ (v ^ ε * (k.factorial : ℝ)) / ε ^ k :=
      (le_div_iff₀ (pow_pos hε k)).mpr (by nlinarith [h])
    _ = _ := by ring

/-- Exponential tilting controls every logarithmic correction moment. -/
theorem smoothCorrection_log_moment_le (E S : Finset ℕ) (k : ℕ)
    (z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) * (Real.log n) ^ k) ≤
      ((k.factorial : ℝ) / ε ^ k) *
        ∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) ^ (1 - ε) := by
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  calc
    _ ≤ (|smoothCorrection E z n| / (n : ℝ)) *
        (((k.factorial : ℝ) / ε ^ k) * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (log_pow_le_rpow k hn1 hε) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hnpos, Real.rpow_one]
      field_simp

/-- The absolute constant in the roughness bound works for every fixed
moment order; only the factorial and extra logarithmic power change. -/
theorem smoothCorrection_log_moments_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (S : Finset ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      (∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| / (n : ℝ) *
        (Real.log n) ^ k) ≤
        A * (k.factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + k) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_shifted_bound hM
  refine ⟨A, hA, fun P S z k hP hlog hz hzhalf => ?_⟩
  have hlogpos : 0 < Real.log P := by linarith
  calc
    _ ≤ ((k.factorial : ℝ) / (1 / Real.log P) ^ k) *
        ∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| /
          (n : ℝ) ^ (1 - 1 / Real.log P) :=
      smoothCorrection_log_moment_le _ _ k z (by positivity)
    _ ≤ ((k.factorial : ℝ) / (1 / Real.log P) ^ k) *
        (A * (Real.log P) ^ (Real.exp 1)) :=
      mul_le_mul_of_nonneg_left (hbound P S z hP hlog hz hzhalf) (by positivity)
    _ = _ := by
      rw [Real.rpow_add hlogpos, Real.rpow_natCast]
      simp only [one_div, inv_pow, div_inv_eq_mul]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CorrectionMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coefficients' actual logarithmic moments

These are absolutely convergent series of the smooth correction.
The bounds are uniform in the moving cutoff and every fixed moment order.
-/

namespace JointDickman

open Finset

theorem correctionLogTerm_norm (E : Finset ℕ) (z : ℝ) (k n : ℕ) :
    ‖correctionLogTerm E z k n‖ =
      |smoothCorrection E z n| / (n : ℝ) * (Real.log n) ^ k := by
  rw [correctionLogTerm, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)]

theorem correctionLogTerm_summable (E : Finset ℕ) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (k : ℕ) :
    Summable (fun n => ‖correctionLogTerm E z k n‖) := by
  have hbase := (smoothCorrection_abs_hasSum E hz hz1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).summable
  have hdom : Summable (fun n => ((k.factorial : ℝ) / (1 / 2 : ℝ) ^ k) *
      (|smoothCorrection E z n| / (n : ℝ) ^ (1 - (1 / 2 : ℝ)))) := by
    simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
      hbase.mul_left ((k.factorial : ℝ) / (1 / 2 : ℝ) ^ k)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hdom
  intro n
  rw [correctionLogTerm_norm]
  simpa using smoothCorrection_log_moment_le E {n} k z (by norm_num : (0 : ℝ) < 1 / 2)

theorem correctionLogMoment_zero (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    correctionLogMoment E z 0 =
      ∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹ := by
  simpa [correctionLogMoment, correctionLogTerm] using
    (smoothCorrection_zeroth_moment E hz).tsum_eq

/-- The fixed-order coefficient moments are bounded with one absolute
logarithmic exponent. -/
theorem correctionLogMoment_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      |correctionLogMoment (Nat.primesLE P) z k| ≤
        A * (k.factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + k) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_log_moments_bound hM
  refine ⟨A, hA, fun P z k hP hlog hz hzhalf => ?_⟩
  have hsum := correctionLogTerm_summable (Nat.primesLE P) hz (by linarith) k
  have hnorm := hsum.tsum_le_of_sum_le (fun S => by
    simpa only [correctionLogTerm_norm] using hbound P S z k hP hlog hz hzhalf)
  calc
    _ = ‖∑' n, correctionLogTerm (Nat.primesLE P) z k n‖ := by
      rw [Real.norm_eq_abs, correctionLogMoment]
    _ ≤ ∑' n, ‖correctionLogTerm (Nat.primesLE P) z k n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ _ := hnorm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CorrectionTails
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the logarithmic correction moments

Half of the exponential tilt absorbs the logarithmic moment; the other
half yields decay in the truncation point.
-/

namespace JointDickman

open Finset

theorem log_pow_tail_bound (k : ℕ) {v V ε : ℝ}
    (hv : 1 ≤ v) (hV : 0 < V) (hVv : V ≤ v) (hε : 0 < ε) :
    (Real.log v) ^ k ≤
      ((k.factorial : ℝ) / (ε / 2) ^ k / V ^ (ε / 2)) * v ^ ε := by
  have hhalf : 0 < ε / 2 := by positivity
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hcut := Real.rpow_le_rpow hV.le hVv hhalf.le
  have hlog := log_pow_le_rpow k hv hhalf
  have hfact : 0 ≤ (k.factorial : ℝ) / (ε / 2) ^ k := by positivity
  have hmul := mul_le_mul hlog hcut (Real.rpow_nonneg hV.le _) (mul_nonneg hfact
    (Real.rpow_nonneg hv0.le _))
  have hsquare : v ^ (ε / 2) * v ^ (ε / 2) = v ^ ε := by
    rw [← Real.rpow_add hv0]
    congr 1
    ring
  have hquot := (le_div_iff₀ (Real.rpow_pos_of_pos hV _)).mpr hmul
  calc
    _ ≤ (((k.factorial : ℝ) / (ε / 2) ^ k * v ^ (ε / 2)) * v ^ (ε / 2)) /
        V ^ (ε / 2) := hquot
    _ = _ := by rw [mul_assoc, hsquare]; ring

theorem correctionLogTerm_tail_bound (E : Finset ℕ) (z : ℝ) (k : ℕ)
    {n : ℕ} {V ε : ℝ} (hV : 0 < V) (hn : V ≤ n) (hε : 0 < ε) :
    ‖correctionLogTerm E z k n‖ ≤
      ((k.factorial : ℝ) / (ε / 2) ^ k / V ^ (ε / 2)) *
        (|smoothCorrection E z n| / (n : ℝ) ^ (1 - ε)) := by
  have hn0 : (0 : ℝ) < n := hV.trans_le hn
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  rw [correctionLogTerm_norm]
  calc
    _ ≤ (|smoothCorrection E z n| / (n : ℝ)) *
        (((k.factorial : ℝ) / (ε / 2) ^ k / V ^ (ε / 2)) * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (log_pow_tail_bound k hn1 hV hn hε) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hn0, Real.rpow_one]
      field_simp

/-- A uniform quantitative error when replacing a truncated correction
moment by its convergent full value. -/
theorem correctionLogMoment_tail_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P V : ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 < V → 0 ≤ z → z ≤ 1 / 2 →
      |correctionLogMoment (Nat.primesLE P) z k -
        ∑ n ∈ range (V + 1), correctionLogTerm (Nat.primesLE P) z k n| ≤
          ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
            (V : ℝ) ^ ((1 / Real.log P) / 2)) *
              (A * (Real.log P) ^ (Real.exp 1)) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_shifted_bound hM
  refine ⟨A, hA, fun P V z k hP hlog hV hz hzhalf => ?_⟩
  let E := Nat.primesLE P
  let ε := 1 / Real.log (P : ℝ)
  let D := (k.factorial : ℝ) / (ε / 2) ^ k / (V : ℝ) ^ (ε / 2)
  let f := correctionLogTerm E z k
  let g := fun n : ℕ => |smoothCorrection E z n| / (n : ℝ) ^ (1 - ε)
  have hε : 0 < ε := by dsimp [ε] <;> positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by linarith)).mpr hlog
  have hVreal : (0 : ℝ) < V := by exact_mod_cast hV
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  have hg : Summable g :=
    (smoothCorrection_abs_hasSum E hz (by linarith) (by linarith : 0 ≤ 1 - ε)).summable
  have hf := correctionLogTerm_summable E hz (by linarith) k
  have hnorm : Summable (fun n : {n // n ∉ range (V + 1)} => ‖f n‖) := hf.subtype _
  have hgD : Summable (fun n => D * g n) := hg.mul_left D
  have hcomparison : (∑' n : {n // n ∉ range (V + 1)}, ‖f n‖) ≤
      ∑' n : ℕ, D * g n := by
    apply Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun n _ => mul_nonneg hD (by dsimp [g] <;> positivity)) _ hnorm hgD
    intro n
    have hnV : V < n.val := by
      have hnrange := n.property
      simp only [mem_range] at hnrange
      omega
    exact correctionLogTerm_tail_bound E z k hVreal (by exact_mod_cast hnV.le) hε
  have htotal : (∑' n, g n) ≤ A * (Real.log P) ^ (Real.exp 1) := by
    apply hg.tsum_le_of_sum_le
    intro S
    exact hbound P S z hP hlog hz hzhalf
  have hsplit := hf.of_norm.sum_add_tsum_subtype_compl (range (V + 1))
  have heq : correctionLogMoment E z k - ∑ n ∈ range (V + 1), f n =
      ∑' n : {n // n ∉ range (V + 1)}, f n := by
    change (∑' n, f n) - _ = _
    linarith [hsplit]
  change |correctionLogMoment E z k - ∑ n ∈ range (V + 1), f n| ≤ D * _
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' n : {n // n ∉ range (V + 1)}, ‖f n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, D * g n := hcomparison
    _ = D * ∑' n, g n := hg.tsum_mul_left D
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal hD

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RpowTaylor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform power expansion for removing roughness

Taylor expansion is made on the fixed compact interval `[0, 1/2]`.
Its coefficients are independent of the expansion order and of the
moving logarithmic scale.
-/

namespace JointDickman

open Finset Set

theorem rpowShift_contDiff (a : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun t : ℝ => (1 - t) ^ a) (Icc 0 (1 / 2)) := by
  apply ContDiffOn.rpow_const_of_ne
  · exact contDiffOn_const.sub contDiffOn_id
  · intro t ht
    linarith [ht.2]

theorem rpowShift_taylor_eval (a t : ℝ) (H : ℕ) :
    taylorWithinEval (fun u : ℝ => (1 - u) ^ a) H (Icc 0 (1 / 2)) 0 t =
      ∑ k ∈ range (H + 1), rpowShiftCoeff a k * t ^ k := by
  rw [taylor_within_apply]
  apply sum_congr rfl
  intro k _
  simp only [sub_zero, smul_eq_mul, rpowShiftCoeff]
  ring

theorem rpowShift_remainder (a : ℝ) (H : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
      |(1 - t) ^ a - ∑ k ∈ range (H + 1), rpowShiftCoeff a k * t ^ k| ≤
        C * t ^ (H + 1) := by
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (rpowShift_contDiff a (H + 1))
  refine ⟨max C 0, le_max_right _ _, fun t ht ht1 => ?_⟩
  have h := hC t ⟨ht, ht1⟩
  rw [Real.norm_eq_abs, rpowShift_taylor_eval, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg ht _))

theorem rpowShift_scaled_term (a L v : ℝ) (k : ℕ) (hL : 0 < L) :
    L ^ a * (rpowShiftCoeff a k * (v / L) ^ k) =
      rpowShiftCoeff a k * v ^ k * L ^ (a - k) := by
  rw [Real.rpow_sub hL, Real.rpow_natCast, div_pow]
  ring

/-- The power expansion with an error uniform throughout `0 ≤ v ≤ L/2`.
The exponent `a` is arbitrary; the application uses `a = z - 1 - j`. -/
theorem rpow_scaled_remainder (a : ℝ) (H : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L v : ℝ, 0 < L → 0 ≤ v → v ≤ L / 2 →
      |(L - v) ^ a - ∑ k ∈ range (H + 1),
        rpowShiftCoeff a k * v ^ k * L ^ (a - k)| ≤
          C * L ^ (a - (H + 1)) * v ^ (H + 1) := by
  obtain ⟨C, hC, hbound⟩ := rpowShift_remainder a H
  refine ⟨C, hC, fun L v hL hv hvL => ?_⟩
  have ht : 0 ≤ v / L := div_nonneg hv hL.le
  have ht1 : v / L ≤ 1 / 2 := (div_le_iff₀ hL).mpr (by linarith)
  have hfactor : (L - v) ^ a = L ^ a * (1 - v / L) ^ a := by
    rw [← Real.mul_rpow hL.le (by linarith : 0 ≤ 1 - v / L)]
    congr 1
    field_simp
  have hsum : (∑ k ∈ range (H + 1), rpowShiftCoeff a k * v ^ k * L ^ (a - k)) =
      L ^ a * ∑ k ∈ range (H + 1), rpowShiftCoeff a k * (v / L) ^ k := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    exact (rpowShift_scaled_term a L v k hL).symm
  rw [hfactor, hsum, ← mul_sub, abs_mul, abs_of_nonneg (Real.rpow_nonneg hL.le a)]
  calc
    _ ≤ L ^ a * (C * (v / L) ^ (H + 1)) :=
      mul_le_mul_of_nonneg_left (hbound _ ht ht1) (Real.rpow_nonneg hL.le a)
    _ = _ := by
      rw [Real.rpow_sub hL,
        show (H : ℝ) + 1 = ((H + 1 : ℕ) : ℝ) by norm_cast,
        Real.rpow_natCast, div_pow]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedPowerExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Taylor expansion inside the correction convolution

This is the finite-sum expansion before the truncated moments are
replaced by their convergent infinite-series values.
-/

namespace JointDickman

open Finset

theorem truncatedLogMoment_eq_range (E : Finset ℕ) (z : ℝ) (V k : ℕ) :
    truncatedLogMoment E z V k = ∑ v ∈ range (V + 1), correctionLogTerm E z k v := by
  have hset : insert 0 (Ioc 0 V) = range (V + 1) := by
    ext n
    simp only [mem_insert, mem_Ioc, mem_range]
    omega
  rw [← hset, sum_insert (by simp)]
  simp [truncatedLogMoment, correctionLogTerm]

theorem correction_expansion_reindex (E : Finset ℕ) (z a L : ℝ) (V H : ℕ) :
    (∑ k ∈ range (H + 1), rpowShiftCoeff a k * truncatedLogMoment E z V k * L ^ (a - k)) =
      ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
        ∑ k ∈ range (H + 1), rpowShiftCoeff a k * (Real.log v) ^ k * L ^ (a - k) := by
  unfold truncatedLogMoment correctionLogTerm
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro k _
  ring

/-- Expansion using the full correction moments. Both errors are explicit:
the Taylor remainder and the exponentially tilted tails of the moments. -/
theorem correction_power_expansion_full
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (z a : ℝ) (H : ℕ), 0 ≤ z → z ≤ 1 / 2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (P V : ℕ) (L : ℝ),
        2 ≤ P → 1 ≤ Real.log P → 0 < V → 0 < L →
        (∀ v ∈ Ioc 0 V, Real.log v ≤ L / 2) →
        |(∑ v ∈ Ioc 0 V, smoothCorrection (Nat.primesLE P) z v / (v : ℝ) *
            (L - Real.log v) ^ a) -
          ∑ k ∈ range (H + 1), rpowShiftCoeff a k *
            correctionLogMoment (Nat.primesLE P) z k * L ^ (a - k)| ≤
          C * L ^ (a - (H + 1)) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
            A * (Real.log P) ^ (Real.exp 1) *
              ∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * L ^ (a - k) *
                ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
                  (V : ℝ) ^ ((1 / Real.log P) / 2)) := by
  obtain ⟨A, hA, htail⟩ := correctionLogMoment_tail_bound hM
  obtain ⟨B, hB, hmom⟩ := smoothCorrection_log_moments_bound hM
  refine ⟨A, hA, fun z a H hz hzhalf => ?_⟩
  -- The Taylor constant depends only on the exponent and order.
  obtain ⟨C₀, hC₀, hunit⟩ := rpow_scaled_remainder a H
  refine ⟨C₀ * B * ((H + 1).factorial : ℝ), by positivity,
    fun P V L hP hlog hV hL hsmall => ?_⟩
  let E := Nat.primesLE P
  let T := ∑ k ∈ range (H + 1), rpowShiftCoeff a k * truncatedLogMoment E z V k * L ^ (a - k)
  let F := ∑ k ∈ range (H + 1), rpowShiftCoeff a k * correctionLogMoment E z k * L ^ (a - k)
  have hfirst : |(∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      (L - Real.log v) ^ a) - T| ≤
      C₀ * L ^ (a - (H + 1)) *
        ∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ) * (Real.log v) ^ (H + 1) := by
    dsimp only [T]
    rw [correction_expansion_reindex, ← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro v hv
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
    rw [← mul_sub, abs_mul, abs_div, abs_of_pos hv0]
    exact (mul_le_mul_of_nonneg_left
      (hunit L (Real.log v) hL (Real.log_natCast_nonneg v) (hsmall v hv))
        (by positivity)).trans_eq (by ring)
  have hfirst' : |(∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      (L - Real.log v) ^ a) - T| ≤
      (C₀ * B * ((H + 1).factorial : ℝ)) * L ^ (a - (H + 1)) *
        (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) := by
    apply hfirst.trans
    have h := mul_le_mul_of_nonneg_left
      (hmom P (Ioc 0 V) z (H + 1) hP hlog hz hzhalf)
      (mul_nonneg hC₀ (Real.rpow_nonneg hL.le (a - ((H : ℝ) + 1))))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hsecond : |T - F| ≤ A * (Real.log P) ^ (Real.exp 1) *
      ∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * L ^ (a - k) *
        ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
          (V : ℝ) ^ ((1 / Real.log P) / 2)) := by
    dsimp [T, F]
    rw [← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro k _
    have hk := htail P V z k hP hlog hV hz hzhalf
    rw [← truncatedLogMoment_eq_range, abs_sub_comm] at hk
    have heq : rpowShiftCoeff a k * truncatedLogMoment E z V k * L ^ (a - k) -
        rpowShiftCoeff a k * correctionLogMoment E z k * L ^ (a - k) =
        (rpowShiftCoeff a k * L ^ (a - k)) *
          (truncatedLogMoment E z V k - correctionLogMoment E z k) := by ring
    rw [heq, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hL _)]
    exact (mul_le_mul_of_nonneg_left hk (by positivity)).trans_eq (by ring)
  have heq : (∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      (L - Real.log v) ^ a) - F =
      ((∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) * (L - Real.log v) ^ a) - T) +
        (T - F) := by ring
  change |(∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) * (L - Real.log v) ^ a) - F| ≤ _
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hfirst' hsecond)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients after removal of the small prime factors

Each coefficient is a finite combination of the published fixed-order
Selberg–Delange coefficients and the actual correction moments. The
definition has no dependence on a subsequently chosen truncation order.
-/

namespace JointDickman

open Finset

theorem roughCoefficient_zero (c : ℕ → ℝ) (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    roughCoefficient c E z 0 = c 0 *
      ∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹ := by
  simp [roughCoefficient, correctionLogMoment_zero E hz]

/-- Grouping the Taylor terms by their total degree gives the actual
rough coefficients, with no discarded cross terms. -/
theorem roughCoefficient_expansion (c : ℕ → ℝ) (E : Finset ℕ)
    (z L : ℝ) (H : ℕ) :
    (∑ ν ∈ range (H + 1), roughCoefficient c E z ν * L ^ (z - 1 - ν)) =
      ∑ j ∈ range (H + 1), c j *
        ∑ k ∈ range (H - j + 1), rpowShiftCoeff (z - 1 - j) k *
          correctionLogMoment E z k * L ^ (z - 1 - j - k) := by
  let f := fun j k : ℕ => c j * rpowShiftCoeff (z - 1 - j) k *
    correctionLogMoment E z k * L ^ (z - 1 - j - k)
  calc
    _ = ∑ ν ∈ range (H + 1), ∑ j ∈ range (ν + 1), f j (ν - j) := by
      apply sum_congr rfl
      intro ν _
      rw [roughCoefficient, sum_mul]
      apply sum_congr rfl
      intro j hj
      have hjν : j ≤ ν := by simpa only [mem_range, Nat.lt_succ_iff] using hj
      dsimp [f]
      rw [Nat.cast_sub hjν]
      congr 1
      congr 1
      ring
    _ = ∑ j ∈ range (H + 1), ∑ k ∈ range (H + 1 - j), f j k :=
      sum_range_diag_flip (H + 1) f
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hjH : j ≤ H := by simpa only [mem_range, Nat.lt_succ_iff] using hj
      rw [show H + 1 - j = H - j + 1 by omega, mul_sum]
      apply sum_congr rfl
      intro k _
      dsimp [f]
      ring

/-- Uniform coefficient bound with the absolute exponent supplied by
the correction moment estimate. -/
theorem roughCoefficient_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (c : ℕ → ℝ)
    {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (ν : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, 2 ≤ P → 1 ≤ Real.log P →
      |roughCoefficient c (Nat.primesLE P) z ν| ≤
        C * (Real.log P) ^ (Real.exp 1 + ν) := by
  obtain ⟨A, hA, hmom⟩ := correctionLogMoment_bound hM
  let C := ∑ j ∈ range (ν + 1),
    |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| * A * ((ν - j).factorial : ℝ)
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => by positivity)
  refine ⟨C, hC, fun P hP hlog => ?_⟩
  unfold roughCoefficient
  calc
    _ ≤ ∑ j ∈ range (ν + 1),
        |c j * rpowShiftCoeff (z - 1 - j) (ν - j) *
          correctionLogMoment (Nat.primesLE P) z (ν - j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (ν + 1),
        (|c j * rpowShiftCoeff (z - 1 - j) (ν - j)| * A * ((ν - j).factorial : ℝ)) *
          (Real.log P) ^ (Real.exp 1 + ν) := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      have hpow : (Real.log P) ^ (Real.exp 1 + (ν - j : ℕ)) ≤
          (Real.log P) ^ (Real.exp 1 + ν) := by
        apply Real.rpow_le_rpow_of_exponent_le hlog
        have hsub : ((ν - j : ℕ) : ℝ) ≤ ν := by exact_mod_cast Nat.sub_le ν j
        linarith
      calc
        _ ≤ |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| *
            (A * ((ν - j).factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + (ν - j : ℕ))) :=
          mul_le_mul_of_nonneg_left (hmom P z (ν - j) hP hlog hz hzhalf) (abs_nonneg _)
        _ ≤ |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| *
            (A * ((ν - j).factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + ν)) := by
          gcongr
        _ = _ := by ring
    _ = _ := by rw [← sum_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughSelbergDelange
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the published expansion inside the roughness convolution

The expansion is inserted only below the truncation, where its endpoint
and logarithmic hypotheses hold. The complementary terms remain the
actual convolution tail, already controlled by Rankin's bound.
-/

namespace JointDickman

open Finset

/-- The usual square-root truncation meets both local expansion conditions. -/
theorem square_root_truncation_conditions {Y : ℝ} {V : ℕ}
    (hY : 9 ≤ Y) (hV : (V : ℝ) ^ 2 ≤ Y) :
    V ≤ ⌊Y⌋₊ ∧ ∀ v ∈ Ioc 0 V,
      3 ≤ Y / (v : ℝ) ∧ Real.log Y / 2 ≤ Real.log (Y / (v : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hV0 : (0 : ℝ) ≤ V := Nat.cast_nonneg V
  refine ⟨Nat.le_floor (by nlinarith), fun v hv => ?_⟩
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  have hvV : (v : ℝ) ≤ V := by exact_mod_cast (mem_Ioc.mp hv).2
  have hv2 : (v : ℝ) ^ 2 ≤ Y := by nlinarith
  constructor
  · apply (le_div_iff₀ hv0).mpr
    nlinarith
  · have hlog := Real.log_le_log (sq_pos_of_pos hv0) hv2
    rw [Real.log_pow] at hlog
    rw [Real.log_div hY0.ne' hv0.ne']
    norm_num at hlog
    linarith

theorem roughSquarefreeSummatory_split (E : Finset ℕ) (z Y : ℝ)
    (V : ℕ) (hV : V ≤ ⌊Y⌋₊) :
    roughSquarefreeSummatory E z Y =
      (∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) +
        roughConvolutionTail E z ⌊Y⌋₊ V := by
  unfold roughSquarefreeSummatory
  rw [roughSquarefreeWeight_summatory,
    ← Ioc_union_Ioc_eq_Ioc (Nat.zero_le V) hV, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1
  apply sum_congr rfl
  intro v _
  simp only [squarefreeSummatory, Nat.floor_div_natCast]

theorem smallConvolution_SD_error (E : Finset ℕ) (c : ℕ → ℝ)
    (z Y : ℝ) (H V : ℕ) {C : ℝ} (hC : 0 ≤ C) (hY : 1 < Y)
    (hz : z ≤ 1)
    (hSD : ∀ X : ℝ, 3 ≤ X →
      |squarefreeSummatory z X - X * sdPolynomial c z H (Real.log X)| ≤
        C * X * (Real.log X) ^ (z - 2 - H))
    (hsize : ∀ v ∈ Ioc 0 V, 3 ≤ Y / (v : ℝ))
    (hlog : ∀ v ∈ Ioc 0 V, Real.log Y / 2 ≤ Real.log (Y / (v : ℝ))) :
    |(∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) -
      Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
        sdPolynomial c z H (Real.log (Y / v))| ≤
      C * Y * (Real.log Y / 2) ^ (z - 2 - H) *
        ∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ) := by
  have hlogpos : 0 < Real.log Y / 2 := div_pos (Real.log_pos hY) (by norm_num)
  have hexp : z - 2 - (H : ℝ) ≤ 0 := by linarith [Nat.cast_nonneg H (α := ℝ)]
  have heq : (∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) -
      Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
        sdPolynomial c z H (Real.log (Y / v)) =
      ∑ v ∈ Ioc 0 V, smoothCorrection E z v *
        (squarefreeSummatory z (Y / v) -
          (Y / v) * sdPolynomial c z H (Real.log (Y / v))) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro v _
    ring
  rw [heq, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro v hv
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  have hpow := Real.rpow_le_rpow_of_nonpos hlogpos (hlog v hv) hexp
  rw [abs_mul]
  calc
    _ ≤ |smoothCorrection E z v| *
        (C * (Y / v) * (Real.log (Y / v)) ^ (z - 2 - H)) :=
      mul_le_mul_of_nonneg_left (hSD _ (hsize v hv)) (abs_nonneg _)
    _ ≤ |smoothCorrection E z v| *
        (C * (Y / v) * (Real.log Y / 2) ^ (z - 2 - H)) := by
      gcongr
    _ = _ := by ring

/-- Direct consequence of the published fixed-order expansion, with an
explicit remaining tail and no assumed moving-cutoff estimate. -/
theorem roughSelbergDelange_truncated
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Finset ℕ) (Y : ℝ) (V : ℕ),
        1 < Y → V ≤ ⌊Y⌋₊ →
        (∀ v ∈ Ioc 0 V, 3 ≤ Y / (v : ℝ)) →
        (∀ v ∈ Ioc 0 V, Real.log Y / 2 ≤ Real.log (Y / (v : ℝ))) →
        |roughSquarefreeSummatory E z Y -
          Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
            sdPolynomial c z H (Real.log (Y / v))| ≤
          C * Y * (Real.log Y / 2) ^ (z - 2 - H) *
            (∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ)) +
              |roughConvolutionTail E z ⌊Y⌋₊ V| := by
  obtain ⟨c, hc0, hcpos, horders⟩ := hSD z hz
  refine ⟨c, hc0, hcpos, fun H => ?_⟩
  obtain ⟨C, hC, hbound⟩ := horders H
  refine ⟨C, hC, fun E Y V hY hV hsize hlog => ?_⟩
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have hsmall := smallConvolution_SD_error E c z Y H V hC hY hz1 hbound hsize hlog
  rw [roughSquarefreeSummatory_split E z Y V hV]
  calc
    _ = |((∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) -
        Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
          sdPolynomial c z H (Real.log (Y / v))) +
            roughConvolutionTail E z ⌊Y⌋₊ V| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hsmall (le_refl _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MovingRoughExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The moving-cutoff expansion with explicit errors

The classical expansion, Taylor approximation, and correction-moment
tails are now combined for the actual rough squarefree summatory function.
No moving-cutoff asymptotic is used as an input.
-/

namespace JointDickman

open Finset

/-- For the nonpositive powers occurring here, the moment-tail sum is
bounded by a single fixed logarithmic power. -/
theorem powerExpansionError_le {A C a L : ℝ} {H P V : ℕ}
    (hA : 0 ≤ A) (ha : a ≤ 0) (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log P) (hV : 0 < V) :
    powerExpansionError A C a H P V L ≤
      C * L ^ (a - (H + 1)) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
        A * (∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
          (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 < Real.log P := by linarith
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have hVpow : 0 < (V : ℝ) ^ ((1 / Real.log P) / 2) := Real.rpow_pos_of_pos hV0 _
  have hsum : (∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * L ^ (a - k) *
      ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
        (V : ℝ) ^ ((1 / Real.log P) / 2))) ≤
      (∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
        (Real.log P) ^ H / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
    rw [sum_mul, sum_div]
    apply sum_le_sum
    intro k hk
    have hkH : k ≤ H := by simpa only [mem_range, Nat.lt_succ_iff] using hk
    have hpow : (Real.log P) ^ k ≤ (Real.log P) ^ H := pow_le_pow_right₀ hlog hkH
    have hunit : L ^ (a - k) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith [Nat.cast_nonneg k (α := ℝ)])
    have hc : 0 ≤ |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k := by positivity
    calc
      _ = (|rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
          ((Real.log P) ^ k * L ^ (a - k)) / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
        simp only [div_pow, one_pow]
        field_simp
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hVpow.le
        apply mul_le_mul_of_nonneg_left _ hc
        simpa using mul_le_mul hpow hunit (Real.rpow_nonneg hL0.le _) (by positivity : (0 : ℝ) ≤ (Real.log P) ^ H)
  unfold powerExpansionError
  refine add_le_add (le_refl _) ?_
  calc
    _ ≤ A * (Real.log P) ^ (Real.exp 1) *
        ((∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
          (Real.log P) ^ H / (V : ℝ) ^ ((1 / Real.log P) / 2)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hA (Real.rpow_nonneg hlog0.le _))
    _ = _ := by
      rw [Real.rpow_add hlog0, Real.rpow_natCast]
      ring

theorem correction_sdPolynomial_reindex (c : ℕ → ℝ) (E : Finset ℕ)
    (z Y : ℝ) (H V : ℕ) (hY : 0 < Y) :
    (∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      sdPolynomial c z H (Real.log (Y / v))) =
      ∑ j ∈ range (H + 1), c j * ∑ v ∈ Ioc 0 V,
        smoothCorrection E z v / (v : ℝ) * (Real.log Y - Real.log v) ^ (z - 1 - j) := by
  unfold sdPolynomial
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro v hv
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  rw [Real.log_div hY.ne' hv0.ne']
  ring

/-- The actual expansion with separately identified classical, Rankin,
Taylor, and moment-tail errors. Its coefficients are the defined moments. -/
theorem moving_rough_expansion_explicit
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ A : ℝ, 0 < A ∧ ∀ H : ℕ, ∃ Csd : ℝ, ∃ C : ℕ → ℝ,
        0 ≤ Csd ∧ (∀ j, 0 ≤ C j) ∧ ∀ (P V : ℕ) (Y : ℝ),
          2 ≤ P → 1 ≤ Real.log P → 0 < V → 9 ≤ Y → (V : ℝ) ^ 2 ≤ Y →
          |roughSquarefreeSummatory (Nat.primesLE P) z Y -
            Y * ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
              (Real.log Y) ^ (z - 1 - ν)| ≤
            Csd * Y * (Real.log Y / 2) ^ (z - 2 - H) *
              (∑ v ∈ Ioc 0 V, |smoothCorrection (Nat.primesLE P) z v| / (v : ℝ)) +
              |roughConvolutionTail (Nat.primesLE P) z ⌊Y⌋₊ V| +
              Y * ∑ j ∈ range (H + 1), |c j| *
                powerExpansionError A (C j) (z - 1 - j) (H - j) P V (Real.log Y) := by
  obtain ⟨c, hc0, hcpos, hclassical⟩ := roughSelbergDelange_truncated hSD hz
  obtain ⟨A, hA, hexp⟩ := correction_power_expansion_full hM
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hzhalf : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, A, hA, fun H => ?_⟩
  obtain ⟨Csd, hCsd, hraw⟩ := hclassical H
  have hexists := fun j : ℕ => hexp z (z - 1 - j) (H - j) hz0 hzhalf
  choose C hC hpower using hexists
  refine ⟨Csd, C, hCsd, hC, fun P V Y hP hlogP hV hY hV2 => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 < Y := by linarith
  have hL : 0 < Real.log Y := Real.log_pos hY1
  obtain ⟨hVfloor, hcut⟩ := square_root_truncation_conditions hY hV2
  have hsmall : ∀ v ∈ Ioc 0 V, Real.log v ≤ Real.log Y / 2 := by
    intro v hv
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
    have hh := (hcut v hv).2
    rw [Real.log_div hY0.ne' hv0.ne'] at hh
    linarith
  let W := ∑ v ∈ Ioc 0 V, smoothCorrection (Nat.primesLE P) z v / (v : ℝ) *
    sdPolynomial c z H (Real.log (Y / v))
  let Q := ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
    (Real.log Y) ^ (z - 1 - ν)
  have hfirst := hraw (Nat.primesLE P) Y V hY1 hVfloor
    (fun v hv => (hcut v hv).1) (fun v hv => (hcut v hv).2)
  have hsecond : |W - Q| ≤ ∑ j ∈ range (H + 1), |c j| *
      powerExpansionError A (C j) (z - 1 - j) (H - j) P V (Real.log Y) := by
    dsimp [W, Q]
    rw [correction_sdPolynomial_reindex c _ z Y H V hY0,
      roughCoefficient_expansion, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j hj
    rw [← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact hpower j P V (Real.log Y) hP hlogP hV hL hsmall
  have heq : roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * Q =
      (roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * W) + Y * (W - Q) := by ring
  change |roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * Q| ≤ _
  rw [heq]
  calc
    _ ≤ |roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * W| + |Y * (W - Q)| :=
      abs_add_le _ _
    _ = |roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * W| + Y * |W - Q| := by
      rw [abs_mul, abs_of_pos hY0]
    _ ≤ _ := add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond hY0.le)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughUniformExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform remainder for removal of small primes

The four explicit errors are bounded by one algebraic remainder and one
Rankin remainder. All constants are independent of the cutoff and endpoint.
-/

namespace JointDickman

open Finset

theorem powerTailConstant_nonneg (a : ℝ) (H : ℕ) :
    0 ≤ powerTailConstant a H := sum_nonneg (fun _ _ => by positivity)

theorem powerExpansionError_le_uniform {A C z L : ℝ} {H j P V : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hz : z ≤ 1) (hj : j ≤ H)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log P) (hV : 0 < V) :
    powerExpansionError A C (z - 1 - j) (H - j) P V L ≤
      C * L ^ (z - 2 - H) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
        A * powerTailConstant (z - 1 - j) (H - j) *
          (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hsub : ((H - j : ℕ) : ℝ) = H - j := Nat.cast_sub hj
  have hexp : z - 1 - j - ((H - j : ℕ) + 1) = z - 2 - H := by
    rw [hsub]
    ring
  have hpow1 : (Real.log P) ^ (Real.exp 1 + (H - j + 1 : ℕ)) ≤
      (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hcast : ((H - j + 1 : ℕ) : ℝ) ≤ (H + 1 : ℕ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.sub_le H j) 1
    linarith
  have hpow2 : (Real.log P) ^ (Real.exp 1 + (H - j : ℕ)) ≤
      (Real.log P) ^ (Real.exp 1 + H) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hcast : ((H - j : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le H j
    linarith
  have h := powerExpansionError_le (C := C) (H := H - j) hA (by linarith : z - 1 - j ≤ 0) hL hlog hV
  rw [hexp] at h
  refine h.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_left hpow1 (by positivity)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hpow2
      (mul_nonneg hA (powerTailConstant_nonneg _ _))

/-- A single cutoff-independent bound for the complete moving expansion. -/
theorem moving_rough_expansion_uniform
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (P V : ℕ) (Y : ℝ),
        2 ≤ P → 1 ≤ Real.log P → 0 < V → 9 ≤ Y → 1 ≤ Real.log Y →
        (V : ℝ) ^ 2 ≤ Y →
        |roughSquarefreeSummatory (Nat.primesLE P) z Y -
          Y * ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
            (Real.log Y) ^ (z - 1 - ν)| ≤
          Y * K * ((Real.log Y) ^ (z - 2 - H) *
            (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
            (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2)) := by
  obtain ⟨c, hc0, hcpos, A, hA, hraw⟩ := moving_rough_expansion_explicit hSD hM hz
  obtain ⟨M, hMpos, hmom⟩ := smoothCorrection_log_moments_bound hM
  obtain ⟨T, hTpos, htail⟩ := roughConvolutionTail_shifted_bound hM
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hzhalf : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, fun H => ?_⟩
  obtain ⟨Csd, C, hCsd, hC, hbound⟩ := hraw H
  let E := Csd * M * (2 : ℝ) ^ (-(z - 2 - H))
  let F := ∑ j ∈ range (H + 1), |c j| * C j
  let G := ∑ j ∈ range (H + 1), |c j| * A * powerTailConstant (z - 1 - j) (H - j)
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hF : 0 ≤ F := sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hC j))
  have hG : 0 ≤ G := sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) hA.le) (powerTailConstant_nonneg _ _))
  refine ⟨E + F + T + G, by positivity, fun P V Y hP hlog hV hY hLY hV2 => ?_⟩
  let L := Real.log Y
  let U := L ^ (z - 2 - H) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ))
  let W := (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2)
  have hL : 0 < L := by dsimp [L] <;> linarith
  have hlog0 : 0 < Real.log P := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hU : 0 ≤ U := by dsimp [U] <;> positivity
  have hW : 0 ≤ W := by dsimp [W] <;> positivity
  have hm := hmom P (Ioc 0 V) z 0 hP hlog hz0 hzhalf
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, add_zero] at hm
  have hlogpow : (Real.log P) ^ (Real.exp 1) ≤
      (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hn : (0 : ℝ) ≤ (H + 1 : ℕ) := Nat.cast_nonneg _
    linarith
  have hclassical : Csd * Y * (L / 2) ^ (z - 2 - H) *
      (∑ v ∈ Ioc 0 V, |smoothCorrection (Nat.primesLE P) z v| / (v : ℝ)) ≤
      Y * E * U := by
    calc
      _ ≤ Csd * Y * (L / 2) ^ (z - 2 - H) *
          (M * (Real.log P) ^ (Real.exp 1)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ Csd * Y * (L / 2) ^ (z - 2 - H) *
          (M * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ))) := by gcongr
      _ = _ := by
        dsimp [E, U]
        rw [Real.div_rpow hL.le (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
  have htail' : |roughConvolutionTail (Nat.primesLE P) z ⌊Y⌋₊ V| ≤ Y * T * W := by
    have h := htail P ⌊Y⌋₊ V z hP hlog hV hz0 hzhalf
    have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
    have hp : (V : ℝ) ^ ((1 / Real.log P) / 2) ≤ (V : ℝ) ^ (1 / Real.log P) := by
      apply Real.rpow_le_rpow_of_exponent_le hV1
      have hpos : 0 < 1 / Real.log P := by positivity
      linarith
    have hlogpow' : (Real.log P) ^ (Real.exp 1) ≤
        (Real.log P) ^ (Real.exp 1 + H) := by
      apply Real.rpow_le_rpow_of_exponent_le hlog
      linarith [Nat.cast_nonneg H (α := ℝ)]
    calc
      _ ≤ (⌊Y⌋₊ : ℝ) / (V : ℝ) ^ (1 / Real.log P) *
          (T * (Real.log P) ^ (Real.exp 1)) := h
      _ ≤ Y / (V : ℝ) ^ ((1 / Real.log P) / 2) *
          (T * (Real.log P) ^ (Real.exp 1 + H)) := by
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · exact div_le_div₀ (by positivity) (Nat.floor_le hY0) (by positivity) hp
        · exact mul_le_mul_of_nonneg_left hlogpow' hTpos.le
      _ = _ := by dsimp [W] <;> ring
  have hpowers : (∑ j ∈ range (H + 1), |c j| *
      powerExpansionError A (C j) (z - 1 - j) (H - j) P V L) ≤ F * U + G * W := by
    calc
      _ ≤ ∑ j ∈ range (H + 1), |c j| * (C j * U +
          A * powerTailConstant (z - 1 - j) (H - j) * W) := by
        apply sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hjH : j ≤ H := by simpa only [mem_range, Nat.lt_succ_iff] using hj
        simpa only [U, W, mul_div_assoc, mul_assoc] using
          powerExpansionError_le_uniform hA.le (hC j) (by linarith : z ≤ 1) hjH hLY hlog hV
      _ = _ := by
        dsimp [F, G]
        simp only [mul_add, sum_add_distrib, sum_mul]
        apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intro j _ <;> ring
  have h := hbound P V Y hP hlog hV hY hV2
  change _ ≤ Y * (E + F + T + G) * (U + W)
  refine h.trans ?_
  change _ + _ + Y * _ ≤ _
  have hsum := add_le_add (add_le_add hclassical htail')
    (mul_le_mul_of_nonneg_left hpowers hY0)
  refine hsum.trans ?_
  nlinarith [mul_nonneg hY0 (mul_nonneg (add_nonneg hE hF) hW),
    mul_nonneg hY0 (mul_nonneg (add_nonneg hTpos.le hG) hU)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCutoffTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Choosing the roughness truncation

An integer square-root truncation turns the remaining Rankin error into
an explicit exponential in the endpoint logarithm.
-/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem roughTruncation_bounds {Y : ℝ} (hY : 0 < Y) (hL : 16 ≤ Real.log Y) :
    0 < roughTruncation Y ∧ (roughTruncation Y : ℝ) ^ 2 ≤ Y ∧
      Real.log Y / 4 ≤ Real.log (roughTruncation Y) := by
  let t := Real.exp (Real.log Y / 2)
  have ht0 : 0 < t := Real.exp_pos _
  have ht2 : 2 ≤ t := by
    have h := Real.add_one_le_exp (Real.log Y / 2)
    dsimp [t]
    linarith
  have ht1 : 1 ≤ t := by linarith
  have hV : 0 < roughTruncation Y := Nat.floor_pos.mpr ht1
  have hVle : (roughTruncation Y : ℝ) ≤ t := Nat.floor_le ht0.le
  have hVhalf : t / 2 ≤ (roughTruncation Y : ℝ) := by
    have h := Nat.lt_floor_add_one t
    change t < (roughTruncation Y : ℝ) + 1 at h
    linarith
  refine ⟨hV, ?_, ?_⟩
  · have heq : t ^ 2 = Y := by
      dsimp [t]
      rw [sq, ← Real.exp_add, add_halves, Real.exp_log hY]
    have hV0 : (0 : ℝ) ≤ roughTruncation Y := Nat.cast_nonneg _
    nlinarith
  · have h := Real.log_le_log (div_pos ht0 (by norm_num)) hVhalf
    rw [Real.log_div ht0.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp] at h
    have hlog2 := Real.log_two_lt_d9
    linarith

theorem roughTruncation_rankin {Y : ℝ} {P : ℕ}
    (hY : 0 < Y) (hL : 16 ≤ Real.log Y) (hP : 0 < Real.log P) :
    1 / (roughTruncation Y : ℝ) ^ ((1 / Real.log P) / 2) ≤
      Real.exp (-(Real.log Y / (8 * Real.log P))) := by
  obtain ⟨hV, _, hlogV⟩ := roughTruncation_bounds hY hL
  have hV0 : (0 : ℝ) < roughTruncation Y := by exact_mod_cast hV
  rw [Real.rpow_def_of_pos hV0, one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hlogV
    (show 0 ≤ (1 / Real.log P) / 2 by positivity)
  have heq : (Real.log Y / 4) * ((1 / Real.log P) / 2) =
      Real.log Y / (8 * Real.log P) := by ring
  rw [heq] at h
  linarith

/-- The complete roughness expansion before substituting `P = B^1000`. -/
theorem moving_rough_expansion_exponential
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) (Y : ℝ),
        2 ≤ P → 1 ≤ Real.log P → 9 ≤ Y → 16 ≤ Real.log Y →
        |roughSquarefreeSummatory (Nat.primesLE P) z Y -
          Y * ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
            (Real.log Y) ^ (z - 1 - ν)| ≤
          Y * K * ((Real.log Y) ^ (z - 2 - H) *
            (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
            (Real.log P) ^ (Real.exp 1 + H) *
              Real.exp (-(Real.log Y / (8 * Real.log P)))) := by
  obtain ⟨c, hc0, hcpos, horders⟩ := moving_rough_expansion_uniform hSD hM hz
  refine ⟨c, hc0, hcpos, fun H => ?_⟩
  obtain ⟨K, hK, hbound⟩ := horders H
  refine ⟨K, hK, fun P Y hP hlog hY hL => ?_⟩
  have hY0 : 0 < Y := by linarith
  obtain ⟨hV, hV2, _⟩ := roughTruncation_bounds hY0 hL
  refine (hbound P (roughTruncation Y) Y hP hlog hV hY (by linarith) hV2).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hY0.le hK)
  apply add_le_add (le_refl _)
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (roughTruncation_rankin hY0 hL (by linarith))
    (Real.rpow_nonneg (by linarith) _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughAuxiliaryExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The moving-cutoff expansion on the manuscript's auxiliary scale

The remainder is uniform once `log Y ≥ B^0.89`. Its decay is derived
from the explicit expansion, rather than assumed as an analytic input.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughErrorEnvelope_tendsto {z D : ℝ} {H : ℕ}
    (hH : D + (89 / 100 : ℝ) * (z - 2 - H) < 0) :
    Tendsto (fun B : ℝ => B ^ D * roughErrorEnvelope z H B) atTop (𝓝 0) := by
  let a : ℝ := D + (89 / 100 : ℝ) * (z - 2 - H)
  let C : ℝ := Real.exp 1 + (H + 1 : ℕ)
  have ha : 0 < -a := by dsimp [a] <;> linarith
  have hfirst := (log_power_div_power_tendsto_zero C ha).const_mul ((1000 : ℝ) ^ C)
  have hsecond := (rough_exponential_error_tendsto (by norm_num : (0 : ℝ) < 89 / 100)
    (by norm_num : (0 : ℝ) < 8000)
    (by positivity : 0 ≤ Real.exp 1 + H) D).const_mul
      ((1000 : ℝ) ^ (Real.exp 1 + H))
  have hsum := hfirst.add hsecond
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB
  have hB0 : 0 < B := by linarith
  have hlog : 0 ≤ Real.log B := (Real.log_pos hB).le
  dsimp [roughErrorEnvelope, a, C]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) hlog,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) hlog,
    Real.rpow_neg hB0.le, div_inv_eq_mul, ← Real.rpow_mul hB0.le]
  rw [mul_add, ← mul_assoc (B ^ D), ← Real.rpow_add hB0]
  congr 1 <;> ring

theorem rough_error_at_auxiliaryCutoff {z Y : ℝ} {B H : ℕ}
    (hB : 1 < B) (hz : z ≤ 1) (hY : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y) :
    (Real.log Y) ^ (z - 2 - H) *
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (H + 1 : ℕ)) +
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + H) *
        Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B)))) ≤
      roughErrorEnvelope z H B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hlog : 0 < Real.log B := Real.log_pos hBreal
  have hcut : Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
    simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
    norm_num
  have hexp : z - 2 - (H : ℝ) ≤ 0 := by linarith [Nat.cast_nonneg H (α := ℝ)]
  have hpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hB0 _) hY hexp
  rw [hcut]
  unfold roughErrorEnvelope
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
    apply Real.exp_le_exp.mpr
    have hdiv := div_le_div_of_nonneg_right hY (by positivity : 0 ≤ 8000 * Real.log B)
    convert neg_le_neg hdiv using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring

/-- The full untwisted moving-cutoff estimate, conditional only on the
classical fixed-order expansion and the cited reciprocal-prime estimate. -/
theorem moving_rough_auxiliary_expansion
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (D : ℝ) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
        |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y -
          Y * ∑ ν ∈ range (H + 1),
            roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν *
              (Real.log Y) ^ (z - 1 - ν)| ≤ K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨c, hc0, hcpos, horders⟩ := moving_rough_expansion_exponential hSD hM hz
  obtain ⟨H, hH⟩ := exists_nat_gt (D / (89 / 100 : ℝ))
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have hgap : D + (89 / 100 : ℝ) * (z - 2 - H) < 0 := by
    have hHD : D < (H : ℝ) * (89 / 100 : ℝ) :=
      (div_lt_iff₀ (by norm_num : (0 : ℝ) < 89 / 100)).mp hH
    linarith
  obtain ⟨K, hK, hbound⟩ := horders H
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  have hlim := (roughErrorEnvelope_tendsto hgap).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (B : ℝ) ^ D * roughErrorEnvelope z H B ≤ 1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge : ∀ᶠ B : ℕ in atTop, (16 : ℝ) ≤ (B : ℝ) ^ (89 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 89 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 16)
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlarge, hP, hlog, eventually_gt_atTop 1] with B hs hl hp hlogP hB
  intro Y hY hY9
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have henv : roughErrorEnvelope z H B ≤ (B : ℝ) ^ (-D) := by
    rw [Real.rpow_neg hB0.le, ← one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hB0 D)).mpr (by simpa [mul_comm] using hs)
  calc
    _ ≤ Y * K * ((Real.log Y) ^ (z - 2 - H) *
          (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (H + 1 : ℕ)) +
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + H) *
          Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B))))) :=
      hbound (auxiliaryCutoff B) Y hp hlogP hY9 (hl.trans hY)
    _ ≤ Y * K * roughErrorEnvelope z H B :=
      mul_le_mul_of_nonneg_left (rough_error_at_auxiliaryCutoff hB hz1 hY)
        (mul_nonneg (by linarith) hK)
    _ ≤ Y * K * (B : ℝ) ^ (-D) := mul_le_mul_of_nonneg_left henv (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of the squarefree Selberg–Delange Euler factor

Cancellation of the linear local logarithms proves absolute convergence.
This identifies the same Euler product used in the published leading
coefficient, without assuming its convergence as another input.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem log_one_add_sub_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |-x| < 1 by rw [abs_neg, abs_of_nonneg hx]; linarith) 1
  have hbase : |Real.log (1 + x) - x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_neg, abs_of_nonneg hx, sub_neg_eq_add, sub_eq_add_neg, add_comm] using h
  apply hbase.trans
  apply (div_le_iff₀ (show 0 < 1 - x by linarith)).mpr
  nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem squarefreeEulerFactor_pos {z : ℝ} (hz : 0 ≤ z) {p : ℕ} (hp : p.Prime) :
    0 < squarefreeEulerFactor z p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  apply mul_pos
  · have h := div_nonneg hz hp0.le
    linarith
  · apply Real.rpow_pos_of_pos
    have h := (div_lt_one hp0).mpr hp1
    linarith

theorem squarefreeEulerFactor_log_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {p : ℕ} (hp : p.Prime) :
    |Real.log (squarefreeEulerFactor z p)| ≤ 4 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsub : 0 < 1 - 1 / (p : ℝ) := by
    have h := (div_lt_one hp0).mpr hp1
    linarith
  have hadd : 0 < 1 + z / (p : ℝ) := by positivity
  have hfrac : z / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hrec : 1 / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have h₁ := log_one_add_sub_error (div_nonneg hz hp0.le) hfrac
  have h₂ := log_one_sub_add_error (by positivity : (0 : ℝ) ≤ 1 / p) hrec
  have heq : Real.log (squarefreeEulerFactor z p) =
      (Real.log (1 + z / (p : ℝ)) - z / p) + z *
        (Real.log (1 - 1 / (p : ℝ)) + 1 / p) := by
    rw [squarefreeEulerFactor, Real.log_mul hadd.ne' (Real.rpow_pos_of_pos hsub z).ne',
      Real.log_rpow hsub]
    ring
  rw [heq]
  calc
    _ ≤ |Real.log (1 + z / (p : ℝ)) - z / p| +
        |z * (Real.log (1 - 1 / (p : ℝ)) + 1 / p)| := abs_add_le _ _
    _ ≤ 2 * (z / (p : ℝ)) ^ 2 + z * (2 * (1 / (p : ℝ)) ^ 2) := by
      rw [abs_mul, abs_of_nonneg hz]
      exact add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ hz)
    _ ≤ 4 / (p : ℝ) ^ 2 := by
      have hzsq : z ^ 2 ≤ 1 := by nlinarith
      field_simp
      nlinarith

theorem primeEulerFactor_pos {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 < primeEulerFactor z n := by
  by_cases hn : n.Prime
  · simpa only [primeEulerFactor, ite_eq_left hn] using squarefreeEulerFactor_pos hz hn
  · simp [primeEulerFactor, hn]

theorem primeEulerFactor_log_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun n => Real.log (primeEulerFactor z n)) := by
  have hsum := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 4
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hsum
  intro n
  rw [Real.norm_eq_abs]
  by_cases hn : n.Prime
  · simpa only [primeEulerFactor, ite_eq_left hn, mul_one_div] using squarefreeEulerFactor_log_bound hz hz1 hn
  · simp [primeEulerFactor, hn]

theorem primeEulerFactor_multipliable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Multipliable (primeEulerFactor z) :=
  Real.multipliable_of_summable_log (primeEulerFactor_pos hz) (primeEulerFactor_log_summable hz hz1)

theorem squarefreeEulerProduct_pos {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < ∏' n : ℕ, primeEulerFactor z n := by
  rw [← Real.rexp_tsum_eq_tprod (primeEulerFactor_pos hz) (primeEulerFactor_log_summable hz hz1)]
  exact Real.exp_pos _

theorem squarefreeEulerProduct_eq (z : ℝ) :
    (∏' n : ℕ, primeEulerFactor z n) =
      ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p := by
  calc
    _ = ∏' n : ℕ, ({p : ℕ | p.Prime}.mulIndicator (squarefreeEulerFactor z)) n := by
      apply tprod_congr
      intro n
      by_cases hn : n.Prime <;> simp [primeEulerFactor, Set.mulIndicator, hn]
    _ = _ := (tprod_subtype {p : ℕ | p.Prime} (squarefreeEulerFactor z)).symm

theorem squarefreeEulerProduct_partial (z : ℝ) (N : ℕ) :
    (∏ n ∈ range (N + 1), primeEulerFactor z n) =
      ∏ p ∈ Nat.primesLE N, squarefreeEulerFactor z p := by
  have hset : (range (N + 1)).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp only [mem_filter, mem_range, Nat.mem_primesLE]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpN, hp⟩
      exact ⟨by omega, hp⟩
  simp only [primeEulerFactor]
  rw [← prod_filter, hset]

theorem squarefreeEulerProduct_partial_tendsto {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun N => ∏ p ∈ Nat.primesLE N, squarefreeEulerFactor z p)
      atTop (𝓝 (∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p)) := by
  have h := (primeEulerFactor_multipliable hz hz1).tendsto_prod_tprod_nat.comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, squarefreeEulerProduct_partial, squarefreeEulerProduct_eq] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughLeadingCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The leading coefficient after the roughness cutoff

Mertens' product theorem and the convergent squarefree Euler factor give
the precise constant `exp(-γ z) / Gamma(z)`.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughLeadingCoefficient_identity {z : ℝ} (hz : 0 ≤ z) (P : ℕ) :
    roughLeadingCoefficient z P * (Real.log P) ^ z =
      (squarefreeLeadingConstant z / ∏ p ∈ Nat.primesLE P, squarefreeEulerFactor z p) *
        (Real.log P * ∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))) ^ z := by
  let S := Nat.primesLE P
  have hlocal (p : ℕ) (hp : p ∈ S) : 0 < 1 - 1 / (p : ℝ) := by
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    have hh := (div_lt_one hp0).mpr hp1
    linarith
  have hU : 0 < ∏ p ∈ S, (1 - 1 / (p : ℝ)) := prod_pos hlocal
  have hA : 0 < ∏ p ∈ S, (1 + z / (p : ℝ)) := by
    apply prod_pos
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
    have hh := div_nonneg hz hp0.le
    linarith
  have hF : (∏ p ∈ S, squarefreeEulerFactor z p) =
      (∏ p ∈ S, (1 + z / (p : ℝ))) * (∏ p ∈ S, (1 - 1 / (p : ℝ))) ^ z := by
    simp only [squarefreeEulerFactor, prod_mul_distrib]
    rw [Real.finsetProd_rpow S _ (fun p hp => (hlocal p hp).le)]
  change (squarefreeLeadingConstant z * ∏ p ∈ S, (1 + z / (p : ℝ))⁻¹) *
    (Real.log P) ^ z = (squarefreeLeadingConstant z / ∏ p ∈ S, squarefreeEulerFactor z p) *
      (Real.log P * ∏ p ∈ S, (1 - 1 / (p : ℝ))) ^ z
  rw [hF, Real.mul_rpow (Real.log_natCast_nonneg P) hU.le, prod_inv_distrib]
  have hUz := (Real.rpow_pos_of_pos hU z).ne'
  field_simp [hA.ne', hUz]

/-- Only the cited Mertens product input is used in this normalization. -/
theorem roughLeadingCoefficient_tendsto
    (hM : PublishedInputs.PrimeProductMertensInput) {z : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) :
    Tendsto (fun P => roughLeadingCoefficient z P * (Real.log P) ^ z) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) := by
  let G := ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p
  have hG : 0 < G := by
    dsimp only [G]
    rw [← squarefreeEulerProduct_eq]
    exact squarefreeEulerProduct_pos hz.le hz1
  have hprod : Tendsto (fun P : ℕ => Real.log P *
      ∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    simpa only [← primesLE_eq_filter, Function.comp_def, Nat.floor_natCast] using
      hM.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => squarefreeLeadingConstant z) atTop
      (𝓝 (squarefreeLeadingConstant z))).div
        (squarefreeEulerProduct_partial_tendsto hz.le hz1) hG.ne').mul
          (hprod.rpow_const (Or.inr hz.le))
  have hconstant : squarefreeLeadingConstant z / G *
      Real.exp (-Real.eulerMascheroniConstant) ^ z =
        Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z := by
    change (G / Real.Gamma z) / G * _ = _
    rw [← Real.exp_mul]
    field_simp [hG.ne', (Real.Gamma_pos_of_pos hz).ne']
  rw [hconstant] at h
  exact h.congr' (Eventually.of_forall (fun P => (roughLeadingCoefficient_identity hz.le P).symm))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ScaledRoughCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients in the limiting prime-product density

The zeroth normalized coefficient has the stated limit, and every fixed
higher coefficient vanishes. No residue-distribution assertion is assumed.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primeNormalizer_bounds (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ primeNormalizer E z ∧ primeNormalizer E z ≤ 1 := by
  have hlocal (p : ℕ) (hp : p ∈ E) : 0 ≤ 1 - z / (p : ℝ) ∧ 1 - z / (p : ℝ) ≤ 1 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hE p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hE p hp).one_le
    have hdiv : z / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr (hz1.trans hp1)
    constructor
    · linarith
    · linarith [div_nonneg hz hp0.le]
  exact ⟨prod_nonneg (fun p hp => (hlocal p hp).1),
    Finset.prod_le_one (fun p hp => (hlocal p hp).1) (fun p hp => (hlocal p hp).2)⟩

theorem roughCoefficient_zero_eq_leading (c : ℕ → ℝ) {z : ℝ}
    (hc : c 0 = squarefreeLeadingConstant z) (hz : |z| < 1) (P : ℕ) :
    roughCoefficient c (Nat.primesLE P) z 0 = roughLeadingCoefficient z P := by
  rw [roughCoefficient_zero c _ hz, hc]
  have hp : (Nat.primesLE P).filter Nat.Prime = Nat.primesLE P :=
    filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  simp only [roughLeadingCoefficient, hp]

theorem auxiliaryRatio_mul_log {B : ℕ} (hB : 1 < B) :
    auxiliaryRatio B * Real.log (auxiliaryCutoff B) = B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hlog : Real.log B ≠ 0 := (Real.log_pos hBreal).ne'
  simp only [auxiliaryRatio, auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
  norm_num
  field_simp

theorem scaledRoughCoefficient_zero_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hz1 : z < 1) :
    Tendsto (fun B => scaledRoughCoefficient c z 0 B) atTop
      (𝓝 ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z))) := by
  have hlead := (roughLeadingCoefficient_tendsto hMP hz hz1.le).comp auxiliaryCutoff_tendsto
  have h := (auxiliary_primeNormalizer_tendsto hM hz.le hz1.le).mul hlead
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hR : 0 ≤ auxiliaryRatio B := (auxiliaryRatio_pos hB).le
  have hlog : 0 ≤ Real.log (auxiliaryCutoff B) := Real.log_natCast_nonneg _
  have hpow : (auxiliaryRatio B) ^ z * (Real.log (auxiliaryCutoff B)) ^ z = (B : ℝ) ^ z := by
    rw [← Real.mul_rpow hR hlog, auxiliaryRatio_mul_log hB]
  unfold scaledRoughCoefficient
  rw [Nat.cast_zero, sub_zero,
    roughCoefficient_zero_eq_leading c hc (by rwa [abs_of_pos hz])]
  dsimp only [Function.comp_def]
  rw [mul_mul_mul_comm, hpow]

theorem scaledRoughCoefficient_succ_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (j : ℕ) :
    Tendsto (fun B => scaledRoughCoefficient c z (j + 1) B) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := roughCoefficient_bound hM c hz hzhalf (j + 1)
  let a : ℝ := (j + 1 : ℕ) - z
  let r : ℝ := Real.exp 1 + (j + 1 : ℕ)
  have ha : 0 < a := by dsimp [a]; push_cast <;> linarith [Nat.cast_nonneg j (α := ℝ)]
  have hlimit := ((log_power_div_power_tendsto_zero r ha).const_mul
    (C * (1000 : ℝ) ^ r)).comp tendsto_natCast_atTop_atTop
  simp only [mul_zero] at hlimit
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlimit
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlogP : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hP, hlogP, eventually_gt_atTop 1] with B hp hlog hB
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hQ := primeNormalizer_bounds _ (auxiliaryPrimes_prime B) hz (by linarith : z ≤ 1)
  have hb := hbound (auxiliaryCutoff B) hp hlog
  rw [Real.norm_eq_abs, scaledRoughCoefficient, abs_mul, abs_mul,
    abs_of_nonneg hQ.1, abs_of_pos (Real.rpow_pos_of_pos hB0 _)]
  calc
    _ ≤ 1 * (C * (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (j + 1 : ℕ))) *
        (B : ℝ) ^ (z - (j + 1 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hQ.2 hb (abs_nonneg _) (by norm_num)) (Real.rpow_nonneg hB0.le _)
    _ = C * (1000 : ℝ) ^ r * ((Real.log B) ^ r / (B : ℝ) ^ a) := by
      have hcut : Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
        simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow] <;> norm_num
      rw [one_mul, hcut, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_pos hBreal).le]
      have hexp : z - (j + 1 : ℕ) = -a := by dsimp [a] <;> ring
      rw [hexp, Real.rpow_neg hB0.le]
      dsimp [r]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform convergence of the prime-product density

Finite combinations of the actual rough coefficients converge uniformly
away from zero. This is the smooth density used for the coarse channel.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem scaledRoughDensity_eq (c : ℕ → ℝ) (z : ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    scaledRoughDensity c z H B s =
      B * primeNormalizer (auxiliaryPrimes B) z *
        roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (B * s) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  unfold scaledRoughDensity roughDensityPolynomial
  rw [← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro j _
  unfold scaledRoughCoefficient
  have hfirst : (B : ℝ) ^ (z - j) = B * (B : ℝ) ^ (z - 1 - j) := by
    rw [show z - (j : ℝ) = 1 + (z - 1 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  have hsecond : (B : ℝ) ^ (z - 1 - j) = B * (B : ℝ) ^ (z - 2 - j) := by
    rw [show z - 1 - (j : ℝ) = 1 + (z - 2 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  rw [Real.mul_rpow hB0.le hs.le, Real.mul_rpow hB0.le hs.le, hfirst]
  have hBn : (B : ℝ) ≠ 0 := hB0.ne'
  field_simp
  rw [hsecond]
  ring

/-- A coefficient limit gives a uniform limit for a fixed negative power. -/
theorem scalar_power_uniform {a δ c : ℝ} {u : ℕ → ℝ}
    (ha : a ≤ 0) (hδ : 0 < δ) (hu : Tendsto u atTop (𝓝 c)) :
    TendstoUniformlyOn (fun (B : ℕ) (s : ℝ) => u B * s ^ a)
      (fun s => c * s ^ a) atTop (Set.Ici δ) := by
  have hnorm : Tendsto (fun n : ℕ => |u n - c| * δ ^ a) atTop (𝓝 0) := by
    simpa using ((hu.sub_const c).abs.mul_const (δ ^ a))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall := hnorm.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall] with B hB
  intro s hs
  have hs0 : 0 < s := hδ.trans_le hs
  have hp := Real.rpow_le_rpow_of_nonpos hδ hs ha
  calc
    dist (c * s ^ a) (u B * s ^ a) = |u B - c| * s ^ a := by
      rw [Real.dist_eq, ← sub_mul, abs_mul, abs_sub_comm,
        abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    _ ≤ |u B - c| * δ ^ a := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ < ε := hB

/-- Finite fixed powers preserve uniform convergence of their coefficients. -/
theorem finite_power_uniform (S : Finset ℕ) (a c : ℕ → ℝ) (u : ℕ → ℕ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (ha : ∀ j ∈ S, a j ≤ 0)
    (hu : ∀ j ∈ S, Tendsto (fun B => u B j) atTop (𝓝 (c j))) :
    TendstoUniformlyOn (fun B s => ∑ j ∈ S, u B j * s ^ a j)
      (fun s => ∑ j ∈ S, c j * s ^ a j) atTop (Set.Ici δ) := by
  induction S using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const (Set.Ici δ)
  | @insert i S hi ih =>
      have hfirst := scalar_power_uniform (ha i (mem_insert_self i S)) hδ (hu i (mem_insert_self i S))
      have hrest := ih (fun j hj => ha j (mem_insert_of_mem hj))
        (fun j hj => hu j (mem_insert_of_mem hj))
      convert hfirst.add hrest using 1 <;> first | (with_reducible_and_instances rfl) | (ext <;> simp [sum_insert hi])

/-- The density converges uniformly on every interval bounded away from zero.
The stronger half-line statement is available because all exponents are negative. -/
theorem scaledRoughDensity_tendstoUniformlyOn
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    TendstoUniformlyOn (fun B s => scaledRoughDensity c z H B s)
      (fun s => ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) * s ^ (z - 1))
      atTop (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b : ℕ → ℝ := fun j => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hfirst := finite_power_uniform (range (H + 1)) (fun j => z - 1 - j) b
    (fun B j => scaledRoughCoefficient c z j B) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => hcoef j)
  have hsecond := finite_power_uniform (range (H + 1)) (fun j => z - 2 - j) (fun _ => 0)
    (fun B j => scaledRoughCoefficient c z j B / B * (z - 1 - j)) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => by
      simpa using ((hcoef j).div_atTop tendsto_natCast_atTop_atTop).mul_const (z - 1 - j))
  convert hfirst.add hsecond using 1
  · rfl
  · funext s
    simp [b, k]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Derivatives of the density used in partial summation

The finite model is differentiated directly, and its first derivative
converges uniformly away from zero along with the density itself.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem hasDerivAt_scaledRoughDensity (c : ℕ → ℝ) (z : ℝ) (H B : ℕ)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (scaledRoughDensity c z H B) (scaledRoughDensityDeriv c z H B s) s := by
  have hfirst : ∀ j ∈ range (H + 1),
      HasDerivAt (fun t => scaledRoughCoefficient c z j B * t ^ (z - 1 - j))
        ((scaledRoughCoefficient c z j B * (z - 1 - j)) * s ^ (z - 2 - j)) s := by
    intro j _
    convert (Real.hasDerivAt_rpow_const (p := z - 1 - j) (Or.inl hs.ne')).const_mul
      (scaledRoughCoefficient c z j B) using 1
    all_goals try with_reducible_and_instances rfl
    rw [show z - 1 - (j : ℝ) - 1 = z - 2 - j by ring]
    ring
  have hsecond : ∀ j ∈ range (H + 1),
      HasDerivAt (fun t => (scaledRoughCoefficient c z j B / B * (z - 1 - j)) * t ^ (z - 2 - j))
        ((scaledRoughCoefficient c z j B / B * (z - 1 - j) * (z - 2 - j)) * s ^ (z - 3 - j)) s := by
    intro j _
    convert (Real.hasDerivAt_rpow_const (p := z - 2 - j) (Or.inl hs.ne')).const_mul
      (scaledRoughCoefficient c z j B / B * (z - 1 - j)) using 1
    all_goals try with_reducible_and_instances rfl
    rw [show z - 2 - (j : ℝ) - 1 = z - 3 - j by ring]
    ring
  exact (HasDerivAt.fun_sum hfirst).add (HasDerivAt.fun_sum hsecond)

theorem scaledRoughDensityDeriv_tendstoUniformlyOn
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    TendstoUniformlyOn (fun B s => scaledRoughDensityDeriv c z H B s)
      (fun s => ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) *
          (z - 1) * s ^ (z - 2)) atTop (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b : ℕ → ℝ := fun j => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hfirst := finite_power_uniform (range (H + 1)) (fun j => z - 2 - j)
    (fun j => b j * (z - 1 - j)) (fun B j => scaledRoughCoefficient c z j B * (z - 1 - j))
    hδ (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)])
    (fun j _ => (hcoef j).mul_const _)
  have hsecond := finite_power_uniform (range (H + 1)) (fun j => z - 3 - j) (fun _ => 0)
    (fun B j => scaledRoughCoefficient c z j B / B * (z - 1 - j) * (z - 2 - j)) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => by
      simpa using (((hcoef j).div_atTop tendsto_natCast_atTop_atTop).mul_const
        (z - 1 - j)).mul_const (z - 2 - j))
  convert hfirst.add hsecond using 1
  · rfl
  · funext s
    simp [b, k]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform boundedness and Lipschitz control of the actual density

These estimates provide the profile hypotheses in the coarse channel.
Their constants are independent of the auxiliary integer B.
-/

namespace JointDickman

open Filter
open scoped Topology NNReal

theorem uniform_power_eventually_bounded {u : ℕ → ℝ → ℝ} {k a δ : ℝ}
    (hδ : 0 < δ) (ha : a ≤ 0)
    (hu : TendstoUniformlyOn u (fun s => k * s ^ a) atTop (Set.Ici δ)) :
    ∀ᶠ B : ℕ in atTop, ∀ s ∈ Set.Ici δ, |u B s| ≤ |k| * δ ^ a + 1 := by
  have h := (Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)
  filter_upwards [h] with B hB
  intro s hs
  have hs0 : 0 < s := hδ.trans_le hs
  have hdist := hB s hs
  rw [Real.dist_eq] at hdist
  have hpow := Real.rpow_le_rpow_of_nonpos hδ hs ha
  calc
    |u B s| = |(u B s - k * s ^ a) + k * s ^ a| := by congr 1; ring
    _ ≤ |u B s - k * s ^ a| + |k * s ^ a| := abs_add_le _ _
    _ = |k * s ^ a - u B s| + |k| * s ^ a := by
      rw [abs_sub_comm, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    _ ≤ |k| * δ ^ a + 1 := by nlinarith [mul_le_mul_of_nonneg_left hpow (abs_nonneg k)]

theorem scaledRoughDensity_bounded_lipschitz
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ L : ℝ≥0, ∀ᶠ B : ℕ in atTop,
      (∀ s ∈ Set.Ici δ, |scaledRoughDensity c z H B s| ≤ M) ∧
      LipschitzOnWith L (scaledRoughDensity c z H B) (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let M := |k| * δ ^ (z - 1) + 1
  let L : ℝ≥0 := ⟨|k * (z - 1)| * δ ^ (z - 2) + 1, by positivity⟩
  have hfun := uniform_power_eventually_bounded hδ (by linarith : z - 1 ≤ 0)
    (scaledRoughDensity_tendstoUniformlyOn hM hMP c hc hz hzhalf hδ H)
  have hder := uniform_power_eventually_bounded hδ (by linarith : z - 2 ≤ 0)
    (scaledRoughDensityDeriv_tendstoUniformlyOn hM hMP c hc hz hzhalf hδ H)
  refine ⟨M, by dsimp [M] <;> positivity, L, ?_⟩
  filter_upwards [hfun, hder] with B hf hd
  refine ⟨hf, ?_⟩
  apply (convex_Ici δ).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun s hs => (hasDerivAt_scaledRoughDensity c z H B (hδ.trans_le hs)).hasDerivWithinAt)
  intro s hs
  change ‖scaledRoughDensityDeriv c z H B s‖₊ ≤ L
  exact_mod_cast hd s hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMeanNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalization of rough summatory means -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughMeanNormalization_nonneg (B : ℕ) (z : ℝ) :
    0 ≤ roughMeanNormalization B z := by
  exact mul_nonneg (Real.log_natCast_nonneg _)
    (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg B)
      (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B))) _)

theorem roughMeanNormalization_ratio {B : ℕ} (hB : 1 < B) (z : ℝ) :
    roughMeanNormalization B z / (B : ℝ) = 1 / auxiliaryRatio B ^ z := by
  have hR := auxiliaryRatio_pos hB
  have hmul := auxiliaryRatio_mul_log hB
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hB)
  have hrpow : auxiliaryRatio B ^ (1 - z) * auxiliaryRatio B ^ z = auxiliaryRatio B := by
    rw [← Real.rpow_add hR]
    simp
  unfold roughMeanNormalization
  apply (div_eq_div_iff hB0 (Real.rpow_pos_of_pos hR z).ne').mpr
  calc
    _ = Real.log (auxiliaryCutoff B) *
        (auxiliaryRatio B ^ (1 - z) * auxiliaryRatio B ^ z) := by ring
    _ = B := by rw [hrpow, mul_comm, hmul]
    _ = _ := by ring

theorem roughMeanNormalization_eventually_le {z : ℝ} (hz : 0 ≤ z) :
    ∀ᶠ B : ℕ in atTop, roughMeanNormalization B z ≤ B := by
  filter_upwards [auxiliaryRatio_tendsto.eventually_ge_atTop 1, eventually_gt_atTop 1]
    with B hR hB
  have hp : auxiliaryRatio B ^ (1 - z) ≤ auxiliaryRatio B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hR (show 1 - z ≤ 1 by linarith)
  calc
    _ ≤ Real.log (auxiliaryCutoff B) * auxiliaryRatio B :=
      mul_le_mul_of_nonneg_left hp (Real.log_natCast_nonneg _)
    _ = B := by rw [mul_comm, auxiliaryRatio_mul_log hB]

theorem roughMeanNormalization_quotient_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => roughMeanNormalization B z /
      (primeNormalizer (auxiliaryPrimes B) z * B)) atTop (𝓝 ((4 : ℝ) ^ z)) := by
  have hlim := (auxiliary_primeNormalizer_tendsto hM hz hz1).inv₀
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (-z)).ne'
  have heq : (fun B => (primeNormalizer (auxiliaryPrimes B) z * auxiliaryRatio B ^ z)⁻¹) =ᶠ[atTop]
      (fun B => roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    conv_rhs => rw [mul_comm (primeNormalizer (auxiliaryPrimes B) z)]
    rw [div_mul_eq_div_div, roughMeanNormalization_ratio hB]
    ring
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)] at hlim
  simpa only [inv_inv] using hlim.congr' heq

theorem roughMeanProfile_eq (c : ℕ → ℝ) (z : ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    roughMeanProfile c z H B s = (B : ℝ) * primeNormalizer (auxiliaryPrimes B) z *
      ∑ j ∈ range (H + 1), roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z j *
        ((B : ℝ) * s) ^ (z - 1 - j) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  unfold roughMeanProfile scaledRoughCoefficient
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [Real.mul_rpow hB0.le hs.le]
  have he : (B : ℝ) ^ (z - j) = B * (B : ℝ) ^ (z - 1 - j) := by
    rw [show z - (j : ℝ) = 1 + (z - 1 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  rw [he]
  ring

theorem roughMeanProfile_eventually_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ B : ℕ in atTop, ∀ s : ℝ, δ ≤ s →
      |roughMeanProfile c z H B s| ≤ M := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b := fun j : ℕ => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hunif := finite_power_uniform (range (H + 1)) (fun j => z - 1 - j) b
    (fun B j => scaledRoughCoefficient c z j B) hδ
    (fun j _ => by linarith [Nat.cast_nonneg (α := ℝ) j]) (fun j _ => hcoef j)
  have hlimit : TendstoUniformlyOn (roughMeanProfile c z H) (fun s => k * s ^ (z - 1))
      atTop (Set.Ici δ) := by
    change TendstoUniformlyOn (fun B s => ∑ j ∈ range (H + 1),
      scaledRoughCoefficient c z j B * s ^ (z - 1 - j)) _ _ _
    simpa [b] using hunif
  refine ⟨|k| * δ ^ (z - 1) + 1, by positivity, ?_⟩
  exact uniform_power_eventually_bounded hδ (by linarith) hlimit

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMeanBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform rough coefficient means on the fixed logarithmic scales -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- The normalized summatory mean is bounded uniformly away from the
zero logarithmic scale. Only the cited classical expansion and prime
estimates are used. -/
theorem rough_normalized_mean_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {z δ : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      9 ≤ Y → δ * B ≤ Real.log Y →
      roughMeanNormalization B z *
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y ≤ C * Y := by
  have hzpos : 0 < z := by rcases hz with rfl | rfl <;> norm_num
  have hzhalf : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  obtain ⟨c, hc, _, H, K, hK, hexp⟩ := moving_rough_auxiliary_expansion hSD hM hz 1
  obtain ⟨M, hM0, hprof⟩ := roughMeanProfile_eventually_bounded hM hMP c hc hzpos hzhalf hδ H
  let J : ℝ := (4 : ℝ) ^ z + 1
  have hJ : 0 ≤ J := by dsimp [J] <;> positivity
  have hquot : ∀ᶠ B : ℕ in atTop,
      |roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)| ≤ J := by
    have h := (roughMeanNormalization_quotient_tendsto hM hzpos.le (by linarith : z ≤ 1)).abs
    simpa only [abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) z)] using
      h.eventually (eventually_le_nhds (lt_add_one |(4 : ℝ) ^ z|))
  have hlow : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(11 / 100 : ℝ)) ≤ δ :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 11 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_le_nhds hδ)
  refine ⟨K + J * M, by positivity, ?_⟩
  filter_upwards [hexp, hprof, hquot, hlow, roughMeanNormalization_eventually_le hzpos.le,
    eventually_gt_atTop 1] with B hexpB hprofB hquotB hlowB hnorm hB
  intro Y hY hlog
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hBnat : 0 < B := lt_trans Nat.zero_lt_one hB
  have hY0 : 0 ≤ Y := by linarith
  have hs : δ ≤ Real.log Y / B := (le_div_iff₀ hB0).mpr hlog
  have hs0 : 0 < Real.log Y / B := hδ.trans_le hs
  have hpower : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y := by
    have hmul := mul_le_mul_of_nonneg_left hlowB hB0.le
    have heq : (B : ℝ) * (B : ℝ) ^ (-(11 / 100 : ℝ)) = (B : ℝ) ^ (89 / 100 : ℝ) := by
      calc
        _ = (B : ℝ) ^ (1 : ℝ) * (B : ℝ) ^ (-(11 / 100 : ℝ)) := by rw [Real.rpow_one]
        _ = (B : ℝ) ^ ((1 : ℝ) + -(11 / 100 : ℝ)) := (Real.rpow_add hB0 _ _).symm
        _ = _ := by norm_num
    rw [heq] at hmul
    exact hmul.trans (by simpa [mul_comm] using hlog)
  have herror := hexpB Y hpower hY
  have hQ : primeNormalizer (auxiliaryPrimes B) z ≠ 0 := by
    apply ne_of_gt
    unfold primeNormalizer
    apply prod_pos
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact sub_pos.mpr ((div_lt_one hp0).mpr (by linarith))
  let T := Y * ∑ j ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z j * (Real.log Y) ^ (z - 1 - j)
  have hmodel : roughMeanNormalization B z * T = Y *
      (roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)) *
        roughMeanProfile c z H B (Real.log Y / B) := by
    rw [roughMeanProfile_eq c z H B hBnat hs0, mul_div_cancel₀ _ hB0.ne']
    dsimp [T]
    field_simp
  have hmodelBound : |roughMeanNormalization B z * T| ≤ Y * (J * M) := by
    rw [hmodel, abs_mul, abs_mul, abs_of_nonneg hY0]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hquotB (hprofB _ hs) (abs_nonneg _) hJ) hY0
  have herrorBound : |roughMeanNormalization B z *
      (roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y - T)| ≤ K * Y := by
    rw [abs_mul, abs_of_nonneg (roughMeanNormalization_nonneg B z)]
    calc
      _ ≤ roughMeanNormalization B z * (K * Y * (B : ℝ) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left herror (roughMeanNormalization_nonneg B z)
      _ ≤ (B : ℝ) * (K * Y * (B : ℝ) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ = _ := by rw [Real.rpow_neg_one]; field_simp
  calc
    _ = roughMeanNormalization B z *
        (roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y - T) +
        roughMeanNormalization B z * T := by ring
    _ ≤ |roughMeanNormalization B z *
        (roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y - T)| +
        |roughMeanNormalization B z * T| := add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ K * Y + Y * (J * M) := add_le_add herrorBound hmodelBound
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual arithmetic coefficient weight A₀ -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_nonneg (B : ℕ) : 0 ≤ coefficientScale B := by
  unfold coefficientScale
  exact mul_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg
    (div_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B))) _)

theorem coefficientWeight_nonneg (B n : ℕ) : 0 ≤ coefficientWeight B n := by
  have hs := coefficientScale_nonneg B
  unfold coefficientWeight roughSquarefreeWeight squarefreeWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs <;> positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First and second moments of the actual coefficient A₀

These are the estimates in equation (5) of the manuscript.  The two
specializations of the published Selberg–Delange input suffice here.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughSquarefreeWeight_sq (E : Finset ℕ) (z : ℝ) (n : ℕ) :
    roughSquarefreeWeight E z n ^ 2 = roughSquarefreeWeight E (z ^ 2) n := by
  simp only [roughSquarefreeWeight, squarefreeWeight, ArithmeticFunction.coe_mk]
  split_ifs <;> simp [← pow_mul, Nat.mul_comm]

theorem coefficientScale_eq_roughMeanNormalization (B : ℕ) :
    coefficientScale B = roughMeanNormalization B (1 / 2) := by
  norm_num [coefficientScale, roughMeanNormalization]

theorem coefficientScale_sq (B : ℕ) (hB : 1 < B) :
    coefficientScale B ^ 2 =
      (Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ)) *
        roughMeanNormalization B (1 / 4) := by
  have hR := auxiliaryRatio_pos hB
  have hhalf : (auxiliaryRatio B ^ (1 / 2 : ℝ)) ^ 2 = auxiliaryRatio B := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  have hquarter : auxiliaryRatio B ^ (1 / 4 : ℝ) *
      auxiliaryRatio B ^ (1 - 1 / 4 : ℝ) = auxiliaryRatio B := by
    rw [← Real.rpow_add hR]
    norm_num
  simp only [coefficientScale, roughMeanNormalization, mul_pow, hhalf]
  rw [mul_mul_mul_comm, hquarter]
  ring

theorem coefficient_second_moment_factor {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop,
      Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ) ≤
        (B : ℝ) ^ (1 / 4 + ε) := by
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (1000 : ℝ) ^ (3 / 4 : ℝ) * (Real.log B) ^ (3 / 4 : ℝ) /
        (B : ℝ) ^ ε ≤ 1 := by
    have h := ((log_power_div_power_tendsto_zero (3 / 4) hε).const_mul
      ((1000 : ℝ) ^ (3 / 4 : ℝ))).comp tendsto_natCast_atTop_atTop
    simp only [mul_zero] at h
    filter_upwards [h.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hB
    simpa [mul_div_assoc] using hB
  filter_upwards [hsmall, eventually_gt_atTop 1] with B hsmallB hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hl : 0 < Real.log (auxiliaryCutoff B) := by
    simpa [auxiliaryCutoff, Nat.cast_pow, Real.log_pow] using
      mul_pos (by norm_num : (0 : ℝ) < 1000)
        (Real.log_pos (show (1 : ℝ) < B by exact_mod_cast hB))
  have hr : auxiliaryRatio B = (B : ℝ) / Real.log (auxiliaryCutoff B) := by
    simp [auxiliaryRatio, auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
  have hpow : Real.log (auxiliaryCutoff B) ^ (3 / 4 : ℝ) ≤ (B : ℝ) ^ ε := by
    simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_natCast_nonneg B)]
    exact (div_le_one (Real.rpow_pos_of_pos hB0 ε)).mp hsmallB
  calc
    _ = (B : ℝ) ^ (1 / 4 : ℝ) * Real.log (auxiliaryCutoff B) ^ (3 / 4 : ℝ) := by
      rw [hr, Real.div_rpow hB0.le hl.le]
      have he : Real.log (auxiliaryCutoff B) /
          Real.log (auxiliaryCutoff B) ^ (1 / 4 : ℝ) =
          Real.log (auxiliaryCutoff B) ^ (3 / 4 : ℝ) := by
        calc
          _ = Real.log (auxiliaryCutoff B) ^ (1 : ℝ) /
              Real.log (auxiliaryCutoff B) ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub hl]; norm_num
      calc
        _ = (B : ℝ) ^ (1 / 4 : ℝ) *
            (Real.log (auxiliaryCutoff B) / Real.log (auxiliaryCutoff B) ^ (1 / 4 : ℝ)) := by ring
        _ = _ := by rw [he]
    _ ≤ (B : ℝ) ^ (1 / 4 : ℝ) * (B : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := (Real.rpow_add hB0 _ _).symm

theorem coefficient_first_moment
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      9 ≤ Y → δ * B ≤ Real.log Y →
      ∑ n ∈ Ioc 0 ⌊Y⌋₊, coefficientWeight B n ≤ C * Y := by
  obtain ⟨C, hC, hbound⟩ := rough_normalized_mean_bound hSD hM hMP (Or.inr rfl) hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with B hboundB
  intro Y hY hlog
  simpa only [coefficientWeight, ← mul_sum, coefficientScale_eq_roughMeanNormalization,
    roughSquarefreeSummatory] using hboundB Y hY hlog

theorem coefficient_second_moment
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      9 ≤ Y → δ * B ≤ Real.log Y →
      ∑ n ∈ Ioc 0 ⌊Y⌋₊, coefficientWeight B n ^ 2 ≤
        C * Y * (B : ℝ) ^ (1 / 4 + ε) := by
  obtain ⟨C, hC, hbound⟩ := rough_normalized_mean_bound hSD hM hMP (Or.inl rfl) hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, coefficient_second_moment_factor hε, eventually_gt_atTop 1]
    with B hboundB hfactor hB
  intro Y hY hlog
  have hY0 : 0 ≤ Y := by linarith
  calc
    _ = coefficientScale B ^ 2 *
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) (1 / 4) Y := by
      simp only [coefficientWeight, mul_pow, roughSquarefreeWeight_sq]
      norm_num [roughSquarefreeSummatory, mul_sum]
    _ = (Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ)) *
        (roughMeanNormalization B (1 / 4) *
          roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) (1 / 4) Y) := by
      rw [coefficientScale_sq B hB, mul_assoc]
    _ ≤ (Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ)) * (C * Y) :=
      mul_le_mul_of_nonneg_left (hboundB Y hY hlog)
        (mul_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg
          (auxiliaryRatio_pos hB).le _))
    _ ≤ (B : ℝ) ^ (1 / 4 + ε) * (C * Y) :=
      mul_le_mul_of_nonneg_right hfactor (mul_nonneg hC hY0)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDensityBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform boundedness of the actual A0 density away from zero -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem auxiliary_half_normalizer_pos (B : ℕ) :
    0 < primeNormalizer (auxiliaryPrimes B) (1/2) := by
  unfold primeNormalizer
  apply prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
  exact sub_pos.mpr ((div_lt_one (by linarith : (0 : ℝ) < p)).mpr (by norm_num <;> linarith))

theorem coefficientDensity_eq_scaled (c : ℕ → ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    coefficientDensity c H B s =
      (coefficientScale B / (primeNormalizer (auxiliaryPrimes B) (1/2)*B))*
        scaledRoughDensity c (1/2) H B s := by
  rw [scaledRoughDensity_eq c (1/2) H B hB hs]
  unfold coefficientDensity
  have hQ := (auxiliary_half_normalizer_pos B).ne'
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditivePhaseVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite partial summation for a nearby additive frequency -/
namespace JointDickman
open Finset

lemma additivePhase_sub_one_norm_le (t : ℝ) :
    ‖additivePhase t-1‖ ≤ 2*Real.pi*|t| := by
  have he : additivePhase t = Complex.exp (Complex.I*((2*Real.pi*t:ℝ):ℂ)) := by
    unfold additivePhase
    congr 1
    push_cast
    ring
  rw [he]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*t)
  simpa [Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos] using h

lemma additivePhase_difference_norm_le (x y : ℝ) :
    ‖additivePhase x-additivePhase y‖ ≤ 2*Real.pi*|x-y| := by
  have he : additivePhase x = additivePhase y*additivePhase (x-y) := by
    rw [←additivePhase_add]
    congr 1
    ring
  rw [he,show additivePhase y*additivePhase (x-y)-additivePhase y =
    additivePhase y*(additivePhase (x-y)-1) by ring,norm_mul,norm_additivePhase,one_mul]
  exact additivePhase_sub_one_norm_le (x-y)

lemma bounded_partial_sums_weighted (z w : ℕ → ℂ) (N : ℕ) (T M L : ℝ)
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hz : ∀ k ≤ N, ‖∑ i ∈ range k, z i‖ ≤ T)
    (hw : ∀ i < N, ‖w i‖ ≤ M)
    (hd : ∀ i < N, ‖w (i+1)-w i‖ ≤ L) :
    ‖∑ i ∈ range N, w i*z i‖ ≤ T*(M+N*L) := by
  cases N with
  | zero => simpa using mul_nonneg hT hM
  | succ N =>
    rw [show (∑ i ∈ range (N+1), w i*z i) = ∑ i ∈ range (N+1), w i • z i by simp]
    rw [sum_range_by_parts]
    simp only [Nat.add_sub_cancel,smul_eq_mul]
    have hf : ‖w N*(∑ i ∈ range (N+1), z i)‖ ≤ M*T := by
      rw [norm_mul]
      exact mul_le_mul (hw N (by omega)) (hz (N+1) le_rfl) (norm_nonneg _) hM
    have hs : ‖∑ i ∈ range N, (w (i+1)-w i)*(∑ j ∈ range (i+1), z j)‖ ≤ (N:ℝ)*(L*T) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _i ∈ range N, L*T := by
          apply sum_le_sum
          intro i hi
          rw [norm_mul]
          exact mul_le_mul (hd i (by have := mem_range.mp hi; omega))
            (hz (i+1) (by have := mem_range.mp hi; omega)) (norm_nonneg _) hL
        _ = _ := by simp
    have hh := (norm_sub_le _ _).trans (add_le_add hf hs)
    apply hh.trans
    push_cast
    nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeMassApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the local odds correction from prime-product masses

For every event, the independent-subset mass differs from the uncorrected
Euler weight by at most the sum of squared selection probabilities.
The resulting prime-tail error is uniform over events.
-/

namespace JointDickman

open Finset

theorem uncorrectedSubsetMass_identity {P S : Finset ℕ} (q : ℕ → ℝ) (hS : S ⊆ P) :
    uncorrectedSubsetMass P q S = bernoulliSubsetMass P q S * ∏ p ∈ S, (1 - q p) := by
  unfold uncorrectedSubsetMass bernoulliSubsetMass
  rw [← prod_sdiff hS (f := fun p => 1 - q p)]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeHarmonicWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact harmonic weights of squarefree prime products

The uncorrected independent-prime mass is the harmonic rough coefficient,
including the empty product. This identifies the weight used in partial summation.
-/

namespace JointDickman

open Finset ArithmeticFunction

theorem primeProduct_squarefree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
  · exact fun p hp => (hS p hp).squarefree

theorem primeProduct_cardFactors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    cardFactors (∏ p ∈ S, p) = S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      have hpprime := hS p (mem_insert_self p S)
      have hrest : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
      rw [prod_insert hp, cardFactors_mul hpprime.ne_zero
        (prod_ne_zero_iff.mpr (fun q hq => (hrest q hq).ne_zero)),
        cardFactors_apply_prime hpprime, ih hrest, card_insert_of_notMem hp]
      omega

theorem uncorrectedSubsetMass_harmonic {P S E : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (hE : Disjoint S E) :
    uncorrectedSubsetMass P (fun p => z / p) S =
      primeNormalizer P z * roughSquarefreeWeight E z (∏ p ∈ S, p) / (∏ p ∈ S, p : ℕ) := by
  have hSP : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS hp)
  have hrough : roughSquarefreeWeight E z (∏ p ∈ S, p) = z ^ S.card := by
    simp only [roughSquarefreeWeight, ArithmeticFunction.coe_mk, Nat.primeFactors_prod hSP,
      hE, ite_eq_left, squarefreeWeight, primeProduct_squarefree S hSP,
      primeProduct_cardFactors S hSP]
  rw [hrough]
  simp only [uncorrectedSubsetMass, primeNormalizer, prod_div_distrib, prod_const, Nat.cast_prod]
  ring

theorem uncorrectedPrimeProductMass_at_product {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    uncorrectedPrimeProductMass P z (∏ p ∈ S, p) = uncorrectedSubsetMass P (fun p => z / p) S := by
  classical
  unfold uncorrectedPrimeProductMass
  rw [sum_eq_single S]
  · simp
  · intro T hT hTS
    have hne : (∏ p ∈ T, p) ≠ ∏ p ∈ S, p :=
      fun heq => hTS (primeProduct_injective hP (mem_powerset.mp hT) hS heq)
    simp [hne]
  · intro hn
    exact False.elim (hn (mem_powerset.mpr hS))

theorem uncorrectedPrimeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    uncorrectedPrimeProductMass P z n = 0 := by
  classical
  apply sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq => hn (mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

theorem uncorrectedPrimeProductMass_harmonic {U : ℝ} {N n : ℕ}
    (hnU : (n : ℝ) ≤ U) (z : ℝ) :
    uncorrectedPrimeProductMass (largePrimeSet U N) z n =
      primeNormalizer (largePrimeSet U N) z * roughSquarefreeWeight (Nat.primesLE N) z n / n := by
  classical
  let P := largePrimeSet U N
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  by_cases hn : n ∈ P.powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hSP, hSn⟩ := mem_image.mp hn
    have hS : S ⊆ P := mem_powerset.mp hSP
    have hd : Disjoint S (Nat.primesLE N) := by
      apply disjoint_left.mpr
      intro p hp hsmall
      have hgt : (N : ℝ) < p := (mem_filter.mp (hS hp)).2
      have hle : p ≤ N := (Nat.mem_primesLE.mp hsmall).1
      exact (not_lt_of_ge (by exact_mod_cast hle)) hgt
    rw [← hSn, uncorrectedPrimeProductMass_at_product z hP hS]
    exact uncorrectedSubsetMass_harmonic z hP hS hd
  · rw [uncorrectedPrimeProductMass_eq_zero z n hn]
    by_cases hd : Disjoint n.primeFactors (Nat.primesLE N)
    · by_cases hsq : Squarefree n
      · have hsub : n.primeFactors ⊆ P := by
          intro p hp
          have hpprime := Nat.prime_of_mem_primeFactors hp
          have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) (Nat.dvd_of_mem_primeFactors hp)
          have hpU : (p : ℝ) ≤ U := (by exact_mod_cast hpn : (p : ℝ) ≤ n).trans hnU
          have hpN : N < p := by
            by_contra hnot
            exact disjoint_left.mp hd hp (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
          exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpU, hpprime⟩, by exact_mod_cast hpN⟩
        exact False.elim (hn (mem_image.mpr ⟨n.primeFactors, mem_powerset.mpr hsub,
          Nat.prod_primeFactors_of_squarefree hsq⟩))
      · simp [roughSquarefreeWeight, hd, squarefreeWeight, hsq]
    · simp [roughSquarefreeWeight, hd]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SelectedPrimeOdds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform odds corrections on bounded prime products -/

namespace JointDickman

open Finset

theorem selectedPrime_card_log_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (S.card : ℝ) * Real.log 2 ≤ Real.log (∏ p ∈ S, p : ℕ) := by
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hS p hp).ne_zero)]
  calc
    _ = ∑ _p ∈ S, Real.log 2 := by simp
    _ ≤ _ := sum_le_sum (fun p hp => Real.log_le_log (by norm_num)
      (by exact_mod_cast (hS p hp).two_le))

theorem inverseSelectedPrimeOdds_le {P z : ℝ} (hP : 0 < P)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hcut : ∀ p ∈ S, P ≤ p) :
    (∏ p ∈ S, (1 - z / (p : ℝ))⁻¹) ≤ Real.exp (2 * (S.card : ℝ) / P) := by
  have hx (p : ℕ) (hp : p ∈ S) : 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    exact ⟨div_nonneg hz hp0.le, (div_le_iff₀ hp0).mpr (by linarith)⟩
  have hsum : (∑ p ∈ S, z / (p : ℝ)) ≤ (S.card : ℝ) / P := by
    calc
      _ ≤ ∑ _p ∈ S, 1 / P := sum_le_sum (fun p hp => by
        have hp0 : (0 : ℝ) < p := hP.trans_le (hcut p hp)
        exact (div_le_div_of_nonneg_right hz1 hp0.le).trans
          (one_div_le_one_div_of_le hP (hcut p hp)))
      _ = _ := by simp [div_eq_mul_inv]
  exact (inverse_product_le_exp S (fun p => z / (p : ℝ)) hx).trans
    (Real.exp_le_exp.mpr (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)))

theorem bernoulliSubsetMass_eq_uncorrected_odds {P S : Finset ℕ} (q : ℕ → ℝ)
    (hS : S ⊆ P) (hq : ∀ p ∈ S, 1 - q p ≠ 0) :
    bernoulliSubsetMass P q S =
      uncorrectedSubsetMass P q S * ∏ p ∈ S, (1 - q p)⁻¹ := by
  rw [uncorrectedSubsetMass_identity q hS, prod_inv_distrib, mul_assoc,
    mul_inv_cancel₀ (prod_ne_zero_iff.mpr hq), mul_one]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryOdds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded odds corrections at the manuscript's auxiliary scale -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_mul_sqrt_ratio {B : ℕ} (hB : 1 < B) :
    coefficientScale B * auxiliaryRatio B ^ (1 / 2 : ℝ) = B := by
  unfold coefficientScale
  rw [mul_assoc, ← Real.rpow_add (auxiliaryRatio_pos hB)]
  norm_num only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  rw [mul_comm, auxiliaryRatio_mul_log hB]

theorem primeNormalizer_coefficientScale_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      primeNormalizer (auxiliaryPrimes B) (1 / 2) ≤ C * coefficientScale B / B := by
  let C : ℝ := (4 : ℝ) ^ (-(1 / 2 : ℝ)) + 1
  have hC : 0 < C := by unfold C; positivity
  refine ⟨C, hC, ?_⟩
  have ht := auxiliary_primeNormalizer_tendsto hM (z := 1 / 2) (by norm_num) (by norm_num)
  filter_upwards [ht.eventually (Iio_mem_nhds (show (4 : ℝ) ^ (-(1 / 2 : ℝ)) < C by
      dsimp [C] <;> linarith)), eventually_gt_atTop 1] with B hQ hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  apply (le_div_iff₀ hB0).mpr
  calc
    _ = (primeNormalizer (auxiliaryPrimes B) (1 / 2) * auxiliaryRatio B ^ (1 / 2 : ℝ)) *
        coefficientScale B := by rw [mul_right_comm, mul_assoc, coefficientScale_mul_sqrt_ratio hB]
    _ ≤ C * coefficientScale B :=
      mul_le_mul_of_nonneg_right hQ.le (coefficientScale_nonneg B)

theorem auxiliary_selected_odds_bound :
    ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp ((16 / 5 : ℝ) * B) →
      (∏ p ∈ S, (1 - (1 / 2 : ℝ) / p)⁻¹) ≤ Real.exp 1 := by
  have ht : Tendsto (fun B : ℕ => (32 / (5 * Real.log 2)) *
      ((B : ℝ) / (auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have hp := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (32 / (5 * Real.log 2))
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using hp
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro S hS hn
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp (hS hp)).1).2
  have hcut : ∀ p ∈ S, (auxiliaryCutoff B : ℝ) ≤ p := by
    intro p hp
    exact (mem_filter.mp (hS hp)).2.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (S.card : ℝ) ≤ (16 / 5 : ℝ) * B / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hn
  apply (inverseSelectedPrimeOdds_le hP (by norm_num) (by norm_num) S hprime hcut).trans
  apply Real.exp_le_exp.mpr
  calc
    2 * (S.card : ℝ) / auxiliaryCutoff B ≤
        2 * ((16 / 5 : ℝ) * B / Real.log 2) / auxiliaryCutoff B := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hP.le
    _ = (32 / (5 * Real.log 2)) * ((B : ℝ) / (auxiliaryCutoff B : ℝ)) := by ring
    _ ≤ 1 := hsmall.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ScaledOscillatoryTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaling the smooth oscillatory test -/

namespace JointDickman

open MeasureTheory

theorem hasDerivAt_scaledOscillatoryTest {w w' : ℝ → ℝ} {ξ X t : ℝ}
    (hw : HasDerivAt w (w' (t / X)) (t / X)) :
    HasDerivAt (scaledOscillatoryTest w ξ X)
      (scaledOscillatoryTestDeriv w w' ξ X t) t := by
  have h := (hasDerivAt_oscillatoryTest (ξ := ξ) hw).scomp t ((hasDerivAt_id t).div_const X)
  change HasDerivAt (fun s => oscillatoryTest w ξ (s / X)) _ t
  simpa only [scaledOscillatoryTestDeriv,
    oscillatoryTestDeriv, Function.comp_def, id_eq, one_div, one_mul, Complex.real_smul,
    Complex.ofReal_inv, div_eq_mul_inv, mul_comm (X : ℂ)⁻¹] using! h

theorem scaledOscillatoryTest_norm_le {w : ℝ → ℝ} {M ξ X t : ℝ}
    (hw : |w (t / X)| ≤ M) : ‖scaledOscillatoryTest w ξ X t‖ ≤ M := by
  simpa only [scaledOscillatoryTest, oscillatoryTest_norm] using hw

theorem scaledOscillatoryTestDeriv_norm_le {w w' : ℝ → ℝ} {M N ξ X t : ℝ}
    (hX : 0 < X) (hw : |w (t / X)| ≤ M) (hw' : |w' (t / X)| ≤ N) :
    ‖scaledOscillatoryTestDeriv w w' ξ X t‖ ≤ (N + 2 * Real.pi * |ξ| * M) / X := by
  simp only [scaledOscillatoryTestDeriv, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hX]
  apply div_le_div_of_nonneg_right _ hX.le
  exact (oscillatoryTestDeriv_norm_le w w' ξ (t / X)).trans
    (add_le_add hw' (mul_le_mul_of_nonneg_left hw (by positivity)))

theorem scaledOscillatoryTestDeriv_continuous {w w' : ℝ → ℝ}
    (hw : Continuous w) (hw' : Continuous w') (ξ X : ℝ) :
    Continuous (scaledOscillatoryTestDeriv w w' ξ X) := by
  have hc := oscillatoryTestDeriv_continuousOn hw.continuousOn hw'.continuousOn ξ
    (s := Set.univ)
  have hglobal := continuousOn_univ.mp hc
  exact (hglobal.comp (continuous_id.div_const X)).div_const _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CompactOscillatorySupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing finite cutoffs for compactly supported tests -/

namespace JointDickman

open Finset MeasureTheory

open Classical in
theorem tsum_eq_Ioc_of_scaled_support {w : ℝ → ℝ} {a b X : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hX : 0 < X)
    (hws : ∀ t, t ≤ a ∨ b < t → w t = 0)
    (f : ℕ → ℂ) (hf : ∀ n : ℕ, w (n / X) = 0 → f n = 0) :
    ∑' n, f n = ∑ n ∈ Ioc ⌊a * X⌋₊ ⌊b * X⌋₊, f n := by
  apply tsum_eq_sum
  intro n hn
  apply hf n
  apply hws
  by_cases hna : n ≤ ⌊a * X⌋₊
  · left
    exact (div_le_iff₀ hX).mpr ((Nat.le_floor_iff (mul_nonneg ha hX.le)).mp hna)
  · right
    have hnb : ⌊b * X⌋₊ < n := by
      have hn' : ¬(⌊a * X⌋₊ < n ∧ n ≤ ⌊b * X⌋₊) := by simpa only [mem_Ioc] using hn
      omega
    exact (lt_div_iff₀ hX).mpr ((Nat.floor_lt (mul_nonneg (ha.trans hab) hX.le)).mp hnb)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient expansion on a fixed scaled support -/

namespace JointDickman

open Filter
open scoped Topology

theorem coefficient_support_window {a : ℝ} (ha : 0 < a) :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      (9 / 10 : ℝ) * B ≤ Real.log X →
      9 ≤ a * X ∧ (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log (a * X) := by
  have hloglim : Tendsto (fun B : ℕ => Real.log a / B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hpowlim : Tendsto (fun B : ℕ => (B : ℝ) ^ (-(11 / 100 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 11 / 100)).comp tendsto_natCast_atTop_atTop
  have hpowlarge : Tendsto (fun B : ℕ => (B : ℝ) ^ (89 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 89 / 100)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hloglim.eventually (Ioi_mem_nhds (by norm_num : -(9 / 20 : ℝ) < 0)),
    hpowlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 9 / 20)),
    hpowlarge.eventually_ge_atTop (Real.log 9), eventually_gt_atTop 0] with B hloga hsmall hlarge hB
  intro X hX hlogX
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hlower : -(9 / 20 : ℝ) * B ≤ Real.log a := (lt_div_iff₀ hB0).mp hloga |>.le
  have hpower : (B : ℝ) ^ (89 / 100 : ℝ) = (B : ℝ) ^ (-(11 / 100 : ℝ)) * B := by
    calc
      _ = (B : ℝ) ^ (-(11 / 100 : ℝ) + 1) := by norm_num
      _ = _ := by rw [Real.rpow_add hB0, Real.rpow_one]
  have hs : (B : ℝ) ^ (89 / 100 : ℝ) ≤ (9 / 20 : ℝ) * B := by
    rw [hpower]
    exact mul_le_mul_of_nonneg_right hsmall.le hB0.le
  have hbound : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log (a * X) := by
    rw [Real.log_mul ha.ne' hX.ne']
    linarith
  exact ⟨(Real.log_le_log_iff (by norm_num) (mul_pos ha hX)).mp (hlarge.trans hbound), hbound⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MultiplicativeExponentialInput
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published multiplicative exponential-sum input

Montgomery--Vaughan, *Exponential sums with multiplicative coefficients*,
Invent. Math. 43 (1977), Corollary 1, DOI 10.1007/BF01390204.
We need only real, everywhere 1-bounded multiplicative coefficients.
These satisfy both hypotheses of the published theorem: the prime bound
and the sum of squares bound. The uniform constant is independent of the
coefficient, hence also of the moving finite set of excluded primes.
-/

namespace JointDickman
open Finset ArithmeticFunction

theorem roughSquarefreeWeight_half_bounded (E : Finset ℕ) (n : ℕ) :
    |roughSquarefreeWeight E (1/2) n| ≤ 1 := by
  simp only [roughSquarefreeWeight,squarefreeWeight,coe_mk]
  split_ifs <;> first
    | exact (abs_of_nonneg (by positivity)).trans_le
        (pow_le_one₀ (by norm_num) (by norm_num))
    | norm_num

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientPartialSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additive partial sums of the actual rough coefficient -/

namespace JointDickman
open Finset

theorem coefficientAdditivePartialSum_factor (B Y : ℕ) (θ : ℝ) :
    coefficientAdditivePartialSum B Y θ = (coefficientScale B : ℂ)*
      ∑ n ∈ Icc 1 Y,
        (roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1/2) n : ℂ)*
          additivePhase ((n : ℝ)*θ) := by
  simp only [coefficientAdditivePartialSum,coefficientWeight,Complex.ofReal_mul,mul_sum]
  apply sum_congr rfl
  intro n _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientScalePower
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subpower loss in the rough coefficient normalization -/

namespace JointDickman
open Filter
open scoped Topology

theorem coefficientScale_power {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, coefficientScale B ≤ (B : ℝ)^(1/2+ε) := by
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (1000 : ℝ)^(1/2 : ℝ)*(Real.log B)^(1/2 : ℝ)/(B : ℝ)^ε ≤ 1 := by
    have hh := ((log_power_div_power_tendsto_zero (1/2) hε).const_mul
      ((1000 : ℝ)^(1/2 : ℝ))).comp tendsto_natCast_atTop_atTop
    have hz : (1000 : ℝ)^(1/2 : ℝ)*0 = 0 := mul_zero _
    rw [hz] at hh
    filter_upwards [hh.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hB
    simpa only [Function.comp_def,mul_div_assoc] using hB
  filter_upwards [hsmall,eventually_gt_atTop 1] with B hsmallB hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hl : 0 < Real.log (auxiliaryCutoff B) := by
    simp only [auxiliaryCutoff,Nat.cast_pow,Real.log_pow]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hB))
  have hr : auxiliaryRatio B = (B : ℝ)/Real.log (auxiliaryCutoff B) := by
    simp [auxiliaryRatio,auxiliaryCutoff,Nat.cast_pow,Real.log_pow]
  have hlog : Real.log (auxiliaryCutoff B)^(1/2 : ℝ) ≤ (B : ℝ)^ε := by
    simp only [auxiliaryCutoff,Nat.cast_pow,Real.log_pow,Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_natCast_nonneg B)]
    exact (div_le_one (Real.rpow_pos_of_pos hB0 ε)).mp hsmallB
  have hid : coefficientScale B =
      (B : ℝ)^(1/2 : ℝ)*Real.log (auxiliaryCutoff B)^(1/2 : ℝ) := by
    unfold coefficientScale
    rw [hr,Real.div_rpow hB0.le hl.le]
    have he : Real.log (auxiliaryCutoff B)/Real.log (auxiliaryCutoff B)^(1/2 : ℝ) =
        Real.log (auxiliaryCutoff B)^(1/2 : ℝ) := by
      calc
        _ = Real.log (auxiliaryCutoff B)^(1 : ℝ)/Real.log (auxiliaryCutoff B)^(1/2 : ℝ) := by
          rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub hl]; norm_num
    calc
      _ = (B : ℝ)^(1/2 : ℝ)*
          (Real.log (auxiliaryCutoff B)/Real.log (auxiliaryCutoff B)^(1/2 : ℝ)) := by ring
      _ = _ := by rw [he]
  rw [hid,Real.rpow_add hB0]
  exact mul_le_mul_of_nonneg_left hlog (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ComplexPartialSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth weights preserve the minor-arc partial-sum bound -/

namespace JointDickman
open Finset MeasureTheory

theorem complex_partial_summation_bound (c : ℕ → ℂ) (φ φ' : ℝ → ℂ)
    {a b D M N : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (_hD : 0 ≤ D) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.Icc a b))
    (hvalue : ∀ t ∈ Set.Icc a b, ‖φ t‖ ≤ M)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖φ' t‖ ≤ N)
    (hpartial : ∀ t ∈ Set.Icc a b, ‖∑ n ∈ Icc 0 ⌊t⌋₊, c n‖ ≤ D) :
    ‖∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n*c n‖ ≤ D*(2*M+N*(b-a)) := by
  have hd : ContinuousOn (deriv φ) (Set.Icc a b) :=
    hφ'.congr (fun t ht => (hφ t ht).deriv)
  have he := sum_mul_eq_sub_sub_integral_mul (c := c) ha hab
    (fun t ht => (hφ t ht).differentiableAt) hd.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at he
  have hint : ‖∫ t in a..b, deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ ≤ N*D*(b-a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t => deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n))
      (C := N*D) (fun t ht => by
        have ht' : t ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc ht
        rw [(hφ t ht').deriv,norm_mul]
        exact mul_le_mul (hderiv t ht') (hpartial t ht') (norm_nonneg _) hN)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh
  have hend (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ ≤ M*D := by
    rw [norm_mul]
    exact mul_le_mul (hvalue t ht) (hpartial t ht) (norm_nonneg _) hM
  rw [he]
  calc
    _ ≤ ‖φ b*(∑ n ∈ Icc 0 ⌊b⌋₊, c n)‖ +
        ‖φ a*(∑ n ∈ Icc 0 ⌊a⌋₊, c n)‖ +
        ‖∫ t in a..b, deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ M*D+M*D+N*D*(b-a) :=
      add_le_add (add_le_add (hend b ⟨hab,le_rfl⟩) (hend a ⟨le_rfl,hab⟩)) hint
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FairSplitChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual finite fair-split channel

A site is a vector of independent Bernoulli bits. Conditional on that site,
each present prime is retained independently with probability one half and
each absent prime stays absent. Integrating two conditionally independent
retentions gives exactly the same-site two-split law, including for arbitrary
output cells. This connects that law to the actual finite channel kernel.
-/

namespace JointDickman

open scoped BigOperators

theorem fairRetentionBitMass_marginal (q : ℝ) (b : Bool) :
    (∑ hit, bernoulliBitMass q hit * fairRetentionBitMass hit b) = bernoulliBitMass (q / 2) b := by
  cases b <;> simp [fairRetentionBitMass, bernoulliBitMass] <;> ring

theorem fairRetentionMass_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y : ι → Bool) :
    (∑ x, bernoulliSiteMass q x * fairRetentionMass x y) =
      bernoulliSiteMass (fun i => q i / 2) y := by
  classical
  simp only [bernoulliSiteMass, fairRetentionMass, finiteProductMass, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i hit => bernoulliBitMass (q i) hit *
    fairRetentionBitMass hit (y i))]
  simp_rw [fairRetentionBitMass_marginal]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetThinning
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fair thinning of an independently selected prime set -/

namespace JointDickman

open Finset

theorem fairRetentionMass_subsets {α : Type*} [DecidableEq α]
    (P : Finset α) (S T : P.powerset) :
    fairRetentionMass (subsetHitEquiv P S) (subsetHitEquiv P T) =
      subsetRetentionMass S.val T.val := by
  classical
  have heq : fairRetentionMass (subsetHitEquiv P S) (subsetHitEquiv P T) =
      ∏ p ∈ P, if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1 := by
    unfold fairRetentionMass finiteProductMass
    calc
      _ = ∏ p : P, if p.val ∈ S.val then (1 / 2 : ℝ) else if p.val ∈ T.val then 0 else 1 := by
        apply prod_congr rfl
        intro p _
        by_cases hs : p.val ∈ S.val <;> by_cases ht : p.val ∈ T.val <;>
          norm_num [subsetHitEquiv, fairRetentionBitMass, bernoulliBitMass, hs, ht]
      _ = _ := prod_coe_sort P (fun p => if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1)

  rw [heq]
  by_cases ht : T.val ⊆ S.val
  · rw [subsetRetentionMass, ite_eq_left ht]
    have hp (p : α) : (if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1) =
        if p ∈ S.val then (1 / 2 : ℝ) else 1 := by
      by_cases hs : p ∈ S.val
      · simp [hs]
      · have hn : p ∉ T.val := fun h => hs (ht h)
        simp [hs, hn]
    simp_rw [hp]
    rw [← prod_filter]
    have hf : P.filter (fun p => p ∈ S.val) = S.val := by
      ext p
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hp => (mem_powerset.mp S.property) hp)
    rw [hf, prod_const]
  · rw [subsetRetentionMass, ite_eq_right ht]
    obtain ⟨p, hpT, hpS⟩ := not_subset.mp ht
    apply prod_eq_zero (mem_powerset.mp T.property hpT)
    simp only [hpT, hpS, ite_false, if_false, ite_true, if_true]

theorem subsetRetentionMass_marginal {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) {T : Finset α} (hT : T ⊆ P) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S * subsetRetentionMass S T) =
      bernoulliSubsetMass P (fun p => q p / 2) T := by
  classical
  let t : P.powerset := ⟨T, mem_powerset.mpr hT⟩
  have h := fairRetentionMass_marginal (fun p : P => q p.val) (subsetHitEquiv P t)
  rw [← (subsetHitEquiv P).sum_comp] at h
  change (∑ s : P.powerset,
    finiteProductMass (fun p : P => bernoulliBitMass (q p.val)) (subsetHitEquiv P s) *
      fairRetentionMass (subsetHitEquiv P s) (subsetHitEquiv P t)) =
    finiteProductMass (fun p : P => bernoulliBitMass (q p.val / 2)) (subsetHitEquiv P t) at h
  simp_rw [bernoulliSubsetMass_eq_product, fairRetentionMass_subsets] at h
  rw [bernoulliSubsetMass_eq_product P (fun p => q p / 2) t] at h
  exact (sum_coe_sort P.powerset (fun S => bernoulliSubsetMass P q S * subsetRetentionMass S T)).symm.trans h

/-- Integrating both the first remaining set and its fair second coins
leaves precisely the independent addition law with halved parameters. -/
theorem subsetRetentionMass_expectation {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (F : Finset α → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S *
      ∑ T ∈ P.powerset, subsetRetentionMass S T * F T) =
      ∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => q p / 2) T * F T := by
  classical
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  rw [← sum_mul, subsetRetentionMass_marginal P q (mem_powerset.mp hT)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDomination
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Manuscript equation (4): domination by the coefficient weight -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- The actual prime-product probability is bounded by A₀(n)/(Bn),
uniformly over the full product range needed by the application. -/
theorem primeProductMass_coefficient_domination
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ n : ℕ, 0 < n →
      (n : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) →
      primeProductMass (auxiliaryPrimes B) (1 / 2) n ≤
        C * coefficientWeight B n / ((B : ℝ) * n) := by
  obtain ⟨C, hC, hQ⟩ := primeNormalizer_coefficientScale_bound hM
  refine ⟨Real.exp 1 * C, mul_pos (Real.exp_pos _) hC, ?_⟩
  filter_upwards [hQ, auxiliary_selected_odds_bound, eventually_gt_atTop 1] with B hQB hodds hB
  intro n hn hsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 ≤ roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n := by
    unfold roughSquarefreeWeight squarefreeWeight
    simp only [ArithmeticFunction.coe_mk]
    split_ifs <;> positivity
  by_cases hs : n ∈ (auxiliaryPrimes B).powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hSP, hSn⟩ := mem_image.mp hs
    have hS : S ⊆ auxiliaryPrimes B := mem_powerset.mp hSP
    have hprime : ∀ p ∈ auxiliaryPrimes B, p.Prime := by
      intro p hp
      exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
    have hnonzero : ∀ p ∈ S, 1 - (1 / 2 : ℝ) / p ≠ 0 := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p (hS hp)).two_le
      have hp0 : (0 : ℝ) < p := by linarith
      have hf : (1 / 2 : ℝ) / p < 1 := (div_lt_one hp0).mpr (by linarith)
      linarith
    have hmass : primeProductMass (auxiliaryPrimes B) (1 / 2) n =
        uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S *
          ∏ p ∈ S, (1 - (1 / 2 : ℝ) / p)⁻¹ := by
      rw [← hSn, primeProductMass_at_product (1 / 2) hprime hS,
        bernoulliSubsetMass_eq_uncorrected_odds _ hS hnonzero]
    have hnU : (n : ℝ) ≤ auxiliaryUpper B := by
      refine hsize.trans (Real.exp_le_exp.mpr ?_)
      nlinarith
    have hunc : uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S =
        primeNormalizer (auxiliaryPrimes B) (1 / 2) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n := by
      rw [← uncorrectedPrimeProductMass_at_product (1 / 2) hprime hS, hSn]
      exact uncorrectedPrimeProductMass_harmonic hnU (1 / 2)
    have hunc0 : 0 ≤ uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S := by
      unfold uncorrectedSubsetMass
      apply mul_nonneg
      · apply prod_nonneg
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
        have hf : (1 / 2 : ℝ) / p ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < p)).mpr (by linarith)
        linarith
      · exact prod_nonneg (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))
    rw [hmass]
    calc
      _ ≤ uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (hodds S hS (by simpa only [hSn] using hsize)) hunc0
      _ = Real.exp 1 * primeNormalizer (auxiliaryPrimes B) (1 / 2) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n := by rw [hunc]; ring
      _ ≤ Real.exp 1 * (C * coefficientScale B / B) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQB (Real.exp_pos _).le) hr) hn0.le
      _ = _ := by unfold coefficientWeight; ring
  · rw [primeProductMass_eq_zero (1 / 2) n hs]
    exact div_nonneg (mul_nonneg (mul_pos (Real.exp_pos _) hC).le (coefficientWeight_nonneg B n))
      (mul_nonneg hB0.le hn0.le)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SignedSplitProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed fair-split product law used by the kernel -/

namespace JointDickman
open Finset

theorem splitProductMass_nonneg (P S : Finset ℕ) (n : ℕ) :
    0 ≤ splitProductMass P S n := by
  classical
  apply sum_nonneg
  intro A _
  unfold subsetRetentionMass
  split_ifs <;> positivity

theorem signedSplitProductMass_one (P : Finset ℕ) (n : ℕ) :
    signedSplitProductMass P (fun _ => 1) n = primeProductMass P (1/2) n := by
  classical
  unfold signedSplitProductMass splitProductMass
  simp only [mul_one]
  rw [subsetRetentionMass_expectation]
  unfold primeProductMass
  apply sum_congr rfl
  intro A _
  have hq : (fun p : ℕ => (1/(p : ℝ))/2) = (fun p : ℕ => (1/2 : ℝ)/(p : ℝ)) := by
    funext p
    ring
  rw [hq]
  split_ifs <;> simp

theorem signedSplitProductMass_abs_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : Finset ℕ → ℝ} (hg : ∀ S ⊆ P, |g S| ≤ 1) (n : ℕ) :
    |signedSplitProductMass P g n| ≤ primeProductMass P (1/2) n := by
  classical
  rw [← signedSplitProductMass_one]
  unfold signedSplitProductMass
  calc
    _ ≤ ∑ S ∈ P.powerset,
        |bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S * g S * splitProductMass P S n| :=
      abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro S hS
      have hmass : 0 ≤ bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S := by
        apply bernoulliSubsetMass_nonneg (mem_powerset.mp hS)
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
        exact ⟨by positivity,(div_le_one (by linarith)).mpr hp1⟩
      rw [abs_mul,abs_mul,abs_of_nonneg hmass,abs_of_nonneg (splitProductMass_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hg S (mem_powerset.mp hS)) hmass)
        (splitProductMass_nonneg _ _ _)

theorem signedSplitProductMass_coefficient_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in Filter.atTop,
      ∀ (g : Finset ℕ → ℝ), (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) →
      |signedSplitProductMass (auxiliaryPrimes B) g n| ≤
        C*coefficientWeight B n/((B : ℝ)*n) := by
  obtain ⟨C,hC,hbound⟩ := primeProductMass_coefficient_domination hM
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with B hboundB
  intro g hg n hn hsize
  exact (signedSplitProductMass_abs_le (auxiliaryPrimes_prime B) hg n).trans
    (hboundB n hn hsize)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointFourierBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First and second Fourier bounds for signed endpoint masses -/

namespace JointDickman
open Finset MeasureTheory

/-- Pointwise domination of each weighted endpoint coefficient. -/
theorem endpoint_weight_domination {B n : ℕ} {a X D M : ℝ}
    {γ : ℕ → ℝ} {w : ℝ → ℝ} (hB : 0 < B) (ha : 0 < a) (hX : 0 < X)
    (hD : 0 ≤ D) (_hM : 0 ≤ M) (hn : a*X < n)
    (hγ : |γ n| ≤ D*coefficientWeight B n/((B : ℝ)*n))
    (hw : |w (n/X)| ≤ M) :
    |γ n*w (n/X)| ≤ (D*M/((B : ℝ)*(a*X)))*coefficientWeight B n := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hn0 : (0 : ℝ) < n := (mul_pos ha hX).trans hn
  have hγ' : |γ n| ≤ D*coefficientWeight B n/((B : ℝ)*(a*X)) :=
    hγ.trans (div_le_div_of_nonneg_left (mul_nonneg hD (coefficientWeight_nonneg B n))
      (mul_pos hB0 (mul_pos ha hX))
      (mul_le_mul_of_nonneg_left hn.le hB0.le))
  rw [abs_mul]
  exact (mul_le_mul hγ' hw (abs_nonneg _)
    (div_nonneg (mul_nonneg hD (coefficientWeight_nonneg B n))
      (mul_pos hB0 (mul_pos ha hX)).le)).trans_eq (by ring)

/-- Finite-window form of both endpoint Fourier estimates. -/
theorem endpoint_fourier_bounds {B : ℕ} {a b X D M : ℝ}
    (hB : 0 < B) (ha : 0 < a) (hX : 0 < X) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ)
    (hγ : ∀ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
      |signedSplitProductMass (auxiliaryPrimes B) g n| ≤
        D*coefficientWeight B n/((B : ℝ)*n))
    (hw : ∀ t, |w t| ≤ M) :
    (∀ θ, ‖endpointFourierSum B a b X g w θ‖ ≤
      (D*M/((B : ℝ)*(a*X)))*∑ n ∈ Ioc 0 ⌊b*X⌋₊, coefficientWeight B n) ∧
    (∫ θ in (0 : ℝ)..1, ‖endpointFourierSum B a b X g w θ‖^2) ≤
      (D*M/((B : ℝ)*(a*X)))^2*∑ n ∈ Ioc 0 ⌊b*X⌋₊, coefficientWeight B n^2 := by
  classical
  let F := D*M/((B : ℝ)*(a*X))
  have hF : 0 ≤ F := by dsimp [F] <;> positivity
  have hdom (n : ℕ) (hn : n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊) :
      |signedSplitProductMass (auxiliaryPrimes B) g n*w (n/X)| ≤ F*coefficientWeight B n := by
    exact endpoint_weight_domination hB ha hX hD hM
      ((Nat.floor_lt (mul_pos ha hX).le).mp (mem_Ioc.mp hn).1) (hγ n hn) (hw _)
  have hsub : Ioc ⌊a*X⌋₊ ⌊b*X⌋₊ ⊆ Ioc 0 ⌊b*X⌋₊ := by
    intro n hn
    simp only [mem_Ioc] at *
    omega
  constructor
  · intro θ
    calc
      _ ≤ ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
          ‖(signedSplitProductMass (auxiliaryPrimes B) g n*w (n/X) : ℝ) *
            additivePhase ((n : ℝ)*θ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊, F*coefficientWeight B n := by
        apply sum_le_sum
        intro n hn
        simpa only [norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_mul] using hdom n hn
      _ ≤ ∑ n ∈ Ioc 0 ⌊b*X⌋₊, F*coefficientWeight B n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg hF (coefficientWeight_nonneg B n))
      _ = _ := (mul_sum _ _ _).symm
  · unfold endpointFourierSum
    rw [finiteAdditiveSum_parseval]
    calc
      _ ≤ ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊, F^2*coefficientWeight B n^2 := by
        apply sum_le_sum
        intro n hn
        rw [Complex.norm_real,Real.norm_eq_abs]
        have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hF (coefficientWeight_nonneg B n))).mpr (hdom n hn)
        simpa only [mul_pow] using hh
      _ ≤ ∑ n ∈ Ioc 0 ⌊b*X⌋₊, F^2*coefficientWeight B n^2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = _ := (mul_sum _ _ _).symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_EndpointScaleWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient range for a fixed scaled endpoint support -/

namespace JointDickman
open Filter
open scoped Topology

theorem endpoint_scale_window {b : ℝ} (hb : 0 < b) :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      (9/10 : ℝ)*B ≤ Real.log X → Real.log X ≤ (5/2 : ℝ)*B →
      9 ≤ b*X ∧ (1/2 : ℝ)*B ≤ Real.log (b*X) ∧
        b*X ≤ Real.exp ((16/5 : ℝ)*B) := by
  have hlo : ∀ᶠ B : ℕ in atTop, -Real.log b ≤ (2/5 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2/5)).eventually_ge_atTop _
  have hhi : ∀ᶠ B : ℕ in atTop, Real.log b ≤ (7/10 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 7/10)).eventually_ge_atTop _
  filter_upwards [hlo,hhi,coefficient_support_window hb] with B hloB hhiB hw
  intro X hX hloglo hloghi
  have he : Real.log (b*X) = Real.log b+Real.log X := Real.log_mul hb.ne' hX.ne'
  refine ⟨(hw X hX hloglo).1,?_,?_⟩
  · rw [he]
    linarith
  · apply (Real.log_le_iff_le_exp (mul_pos hb hX)).mp
    rw [he]
    linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_EndpointFourierMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Manuscript (35) and the trivial endpoint sum bound -/

namespace JointDickman
open Filter Finset MeasureTheory
open scoped Topology

theorem endpoint_fourier_moments
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ᶠ B : ℕ in atTop,
      ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      Real.log X ≤ (5/2 : ℝ)*B →
      ∀ (g : Finset ℕ → ℝ), (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      ∀ (w : ℝ → ℝ) (M : ℝ), 0 ≤ M → (∀ t, |w t| ≤ M) →
      (∀ θ, ‖endpointFourierSum B a b X g w θ‖ ≤ C₁*M/B) ∧
      (∫ θ in (0 : ℝ)..1, ‖endpointFourierSum B a b X g w θ‖^2) ≤
        C₂*M^2*(B : ℝ)^(-7/4+ε)/X := by
  obtain ⟨D,hD,hdom⟩ := signedSplitProductMass_coefficient_bound hM
  obtain ⟨K₁,hK₁,hfirst⟩ := coefficient_first_moment hSD hM hMP (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨K₂,hK₂,hsecond⟩ := coefficient_second_moment hSD hM hMP
    (by norm_num : (0 : ℝ) < 1/2) hε
  have hb : 0 < b := ha.trans_le hab
  refine ⟨D*K₁*b/a,D^2*K₂*b/a^2,by positivity,by positivity,?_⟩
  filter_upwards [hdom,hfirst,hsecond,endpoint_scale_window hb,eventually_gt_atTop 0]
    with B hdomB hfirstB hsecondB hwindow hB
  intro X hX hloglo hloghi g hg w M hM0 hw
  obtain ⟨hY,hlogY,hsize⟩ := hwindow X hX hloglo hloghi
  have hdom' : ∀ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
      |signedSplitProductMass (auxiliaryPrimes B) g n| ≤
        D*coefficientWeight B n/((B : ℝ)*n) := by
    intro n hn
    have hlow : a*X < (n : ℝ) := (Nat.floor_lt (mul_pos ha hX).le).mp (mem_Ioc.mp hn).1
    have hn0 : 0 < n := by exact_mod_cast ((mul_pos ha hX).trans hlow)
    have hnY : (n : ℝ) ≤ b*X := (Nat.le_floor_iff (mul_pos hb hX).le).mp (mem_Ioc.mp hn).2
    exact hdomB g hg n hn0 (hnY.trans hsize)
  obtain ⟨hmax,hL2⟩ := endpoint_fourier_bounds hB ha hX hD.le hM0 g w hdom' hw
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hBne := hB0.ne'
  have hXne := hX.ne'
  have hane := ha.ne'
  constructor
  · intro θ
    refine (hmax θ).trans ?_
    calc
      _ ≤ (D*M/((B : ℝ)*(a*X)))*(K₁*(b*X)) :=
        mul_le_mul_of_nonneg_left (hfirstB _ hY hlogY) (by positivity)
      _ = _ := by field_simp
  · refine hL2.trans ?_
    calc
      _ ≤ (D*M/((B : ℝ)*(a*X)))^2*(K₂*(b*X)*(B : ℝ)^(1/4+ε)) :=
        mul_le_mul_of_nonneg_left (hsecondB _ hY hlogY) (sq_nonneg _)
      _ = _ := by
        have hp : (B : ℝ)^(1/4+ε) = (B : ℝ)^(-7/4+ε)*(B : ℝ)^2 := by
          rw [← Real.rpow_natCast,← Real.rpow_add hB0]
          congr 1
          norm_num
          ring
        rw [hp]
        field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DiscardedRegionBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paying for a discarded frequency region by endpoint square moments -/

namespace JointDickman
open MeasureTheory

/-- Young's inequality gives the needed two-endpoint estimate without
introducing a separate square root of each Parseval bound. -/
theorem discarded_region_integral_bound {F G H : ℝ → ℂ} {E : Set ℝ} {D : ℝ}
    (hE : MeasurableSet E) (hsub : E ⊆ Set.Ioc 0 1) (hD : 0 ≤ D)
    (hF : Continuous F) (hG : Continuous G)
    (hH : ∀ θ ∈ E, ‖H θ‖ ≤ D) :
    ‖∫ θ in E, F θ*G θ*H θ‖ ≤
      D/2*((∫ θ in (0 : ℝ)..1, ‖F θ‖^2)+(∫ θ in (0 : ℝ)..1, ‖G θ‖^2)) := by
  let U : ℝ → ℝ := fun θ => D/2*(‖F θ‖^2+‖G θ‖^2)
  have hU : Continuous U := continuous_const.mul ((hF.norm.pow 2).add (hG.norm.pow 2))
  have hU0 (θ : ℝ) : 0 ≤ U θ := by dsimp [U] <;> positivity
  have hUi : IntegrableOn U (Set.Ioc 0 1) := (hU.intervalIntegrable 0 1).1
  have hUE : IntegrableOn U E := hUi.mono_set hsub
  have hbound (θ : ℝ) (hθ : θ ∈ E) : ‖F θ*G θ*H θ‖ ≤ U θ := by
    rw [norm_mul,norm_mul]
    calc
      _ ≤ (‖F θ‖*‖G θ‖)*D := mul_le_mul_of_nonneg_left (hH θ hθ) (by positivity)
      _ ≤ U θ := by
        have h := sq_nonneg (‖F θ‖-‖G θ‖)
        have hh : ‖F θ‖*‖G θ‖ ≤ (‖F θ‖^2+‖G θ‖^2)/2 := by nlinarith
        have hh' := mul_le_mul_of_nonneg_right hh hD
        dsimp [U]
        nlinarith
  calc
    _ ≤ ∫ θ in E, ‖F θ*G θ*H θ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ in E, U θ := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun θ => norm_nonneg _)) hUE
      (by filter_upwards [ae_restrict_mem hE] with θ hθ; exact hbound θ hθ)
    _ ≤ ∫ θ in Set.Ioc 0 1, U θ := setIntegral_mono_set hUi
      (Filter.Eventually.of_forall hU0) (Filter.Eventually.of_forall hsub)
    _ = _ := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      dsimp [U]
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add]
      · exact (hF.norm.pow 2).intervalIntegrable 0 1
      · exact (hG.norm.pow 2).intervalIntegrable 0 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointFourierReflection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reflecting the second endpoint in the Fourier integral -/

namespace JointDickman
open Finset
open scoped ComplexConjugate

theorem finiteAdditiveSum_neg_real (s : Finset ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    finiteAdditiveSum s (fun n => (c n : ℂ)) (-θ) =
      conj (finiteAdditiveSum s (fun n => (c n : ℂ)) θ) := by
  unfold finiteAdditiveSum
  rw [map_sum]
  apply sum_congr rfl
  intro n _
  rw [map_mul,Complex.conj_ofReal,additivePhase_conj]
  congr 2
  ring

theorem endpointFourierSum_neg_norm (B : ℕ) (a b X : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) (θ : ℝ) :
    ‖endpointFourierSum B a b X g w (-θ)‖ = ‖endpointFourierSum B a b X g w θ‖ := by
  unfold endpointFourierSum
  rw [finiteAdditiveSum_neg_real]
  exact Complex.norm_conj _

theorem endpointFourierSum_continuous (B : ℕ) (a b X : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) :
    Continuous (endpointFourierSum B a b X g w) :=
  finiteAdditiveSum_continuous _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_MinorArcSupportWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The floor cutoffs used by smooth minor-arc partial summation -/

namespace JointDickman
open Filter
open scoped Topology

theorem minorArc_support_window {a b : ℝ} (ha : 0 < a) :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      (9/10 : ℝ)*B ≤ Real.log X →
      (B : ℝ)^12 ≤ X ∧ ∀ t ∈ Set.Icc (a*X) (b*X),
        2 ≤ ⌊t⌋₊ ∧ (B : ℝ)/2 ≤ Real.log (⌊t⌋₊ : ℝ) ∧
          X ≤ (⌊t⌋₊ : ℝ)*(B : ℝ)^2 ∧ (⌊t⌋₊ : ℝ) ≤ b*X := by
  have hpoly : ∀ᶠ B : ℕ in atTop, (B : ℝ)^12 ≤ Real.exp ((9/10 : ℝ)*B) := by
    have hh := (isLittleO_pow_exp_pos_mul_atTop 12
      (by norm_num : (0 : ℝ) < 9/10)).def (by norm_num : (0 : ℝ) < 1)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hh] with B hB
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg B : (0 : ℝ) ≤ B) 12),
      abs_of_pos (Real.exp_pos _),one_mul] using hB
  have hlog : ∀ᶠ B : ℕ in atTop, -Real.log (a/2) ≤ (2/5 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2/5)).eventually_ge_atTop _
  have hpow : ∀ᶠ B : ℕ in atTop, 2/a ≤ (B : ℝ)^2 :=
    ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hpoly,hlog,hpow,coefficient_support_window ha] with B hp hl hB hw
  intro X hX hlogX
  have hexp : Real.exp ((9/10 : ℝ)*B) ≤ X := by
    simpa only [Real.exp_log hX] using Real.exp_le_exp.mpr hlogX
  refine ⟨hp.trans hexp,?_⟩
  intro t ht
  have hlarge : 9 ≤ a*X := (hw X hX hlogX).1
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hfloor : t/2 ≤ (⌊t⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one t
    linarith [ht.1]
  have hlow : a/2*X ≤ (⌊t⌋₊ : ℝ) := by linarith [ht.1]
  have hfloor0 : 0 < (⌊t⌋₊ : ℝ) := (mul_pos (half_pos ha) hX).trans_le hlow
  refine ⟨(Nat.le_floor_iff ht0).mpr (by norm_num <;> linarith [ht.1]),?_,?_,
    (Nat.floor_le ht0).trans ht.2⟩
  · have hh := Real.log_le_log (mul_pos (half_pos ha) hX) hlow
    rw [Real.log_mul (half_pos ha).ne' hX.ne'] at hh
    linarith
  · have hscale : 1 ≤ a/2*(B : ℝ)^2 := by
      have hh := mul_le_mul_of_nonneg_left hB (half_pos ha).le
      have he : a/2*(2/a) = 1 := by field_simp
      rwa [he] at hh
    calc
      X = X*1 := (mul_one _).symm
      _ ≤ X*(a/2*(B : ℝ)^2) := mul_le_mul_of_nonneg_left hscale hX.le
      _ = (a/2*X)*(B : ℝ)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlow (sq_nonneg _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothCoefficientMinorArc
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth minor-arc bound for the actual coefficient, equation (36) -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem coefficient_partial_sum_from_zero (B Y : ℕ) (θ : ℝ) :
    (∑ n ∈ Icc 0 Y, (coefficientWeight B n : ℂ)*additivePhase ((n : ℝ)*θ)) =
      coefficientAdditivePartialSum B Y θ := by
  unfold coefficientAdditivePartialSum
  symm
  apply sum_subset (by intro n hn; simp only [mem_Icc] at *; omega)
  intro n hn hnot
  have hn0 : n = 0 := by simp only [mem_Icc] at *; omega
  subst n
  simp [coefficientWeight]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MinorArcMeasurable
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measurable discarded minor-arc region -/

namespace JointDickman

theorem measurableSet_rationalArcs (Q δ : ℝ) : MeasurableSet {θ | InRationalArc θ Q δ} := by
  have he : {θ | InRationalArc θ Q δ} =
      ⋃ r : ℚ, {θ : ℝ | (r.den : ℝ) ≤ Q ∧ |θ-(r : ℝ)| ≤ δ} := by
    ext θ
    simp [InRationalArc]
  rw [he]
  apply MeasurableSet.iUnion
  intro r
  by_cases hr : (r.den : ℝ) ≤ Q
  · simp only [hr,true_and]
    exact isClosed_le (continuous_id.sub continuous_const).abs continuous_const |>.measurableSet
  · simp only [hr,false_and,Set.ofPred_false]
    exact MeasurableSet.empty

theorem minorArcRegion_measurable (B j : ℕ) (X : ℝ) : MeasurableSet (minorArcRegion B j X) := by
  exact measurableSet_Ioc.inter
    (((measurableSet_rationalArcs ((B : ℝ)^12) ((B : ℝ)^13/X)).preimage
      (continuous_const.mul continuous_id).measurable).compl)

theorem minorArcRegion_subset (B j : ℕ) (X : ℝ) : minorArcRegion B j X ⊆ Set.Ioc 0 1 :=
  fun _ h => h.1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicScaleBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary logarithmic losses used in the minor-arc specialization -/
namespace JointDickman
open Filter
open scoped Topology

theorem eventually_nat_log_linear (A : ℝ) :
    ∀ᶠ B : ℕ in atTop, A*Real.log B ≤ (B:ℝ) := by
  have hlim : Tendsto (fun B : ℕ => A*Real.log B/(B:ℝ)) atTop (𝓝 0) := by
    have h := ((log_power_div_power_tendsto_zero 1 (by norm_num : (0:ℝ) < 1)).const_mul A).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def,Real.rpow_one,mul_zero,mul_div_assoc] using h
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)),
    eventually_ge_atTop 1] with B hsmall hB
  have hB0 : (0:ℝ) < B := by exact_mod_cast hB
  exact (div_le_one hB0).mp hsmall

theorem eventually_nat_one_add_log_power {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : ℕ in atTop, 1+Real.log B ≤ 2*(B:ℝ)^δ := by
  have hlim : Tendsto (fun B : ℕ => Real.log B/(B:ℝ)^δ) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      (log_power_div_power_tendsto_zero 1 hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)),
    eventually_ge_atTop 1] with B hsmall hB
  have hB1 : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hp : 0 < (B:ℝ)^δ := Real.rpow_pos_of_pos (by linarith) δ
  have hl : Real.log B ≤ (B:ℝ)^δ := (div_le_one hp).mp hsmall
  have h1 : 1 ≤ (B:ℝ)^δ := Real.one_le_rpow hB1 hδ.le
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MinorArcStrongApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dirichlet approximation retaining the error on the ambient scale -/
namespace JointDickman

theorem minorArc_strong_rational_approximation {θ Q X : ℝ}
    (hQ : 0 < Q) (hX : Q ≤ X) (hminor : ¬ InRationalArc θ Q (Q/X)) :
    ∃ r : ℚ, Q < (r.den:ℝ) ∧ (r.den:ℝ) ≤ X/Q ∧ |θ-(r:ℝ)| ≤ 1/X := by
  have hX0 : 0 < X := hQ.trans_le hX
  have hratio : 1 ≤ X/Q := (le_div_iff₀ hQ).mpr (by simpa using hX)
  let n := ⌊X/Q⌋₊
  have hn : 0 < n := Nat.floor_pos.mpr hratio
  obtain ⟨r,herr,hden⟩ := Real.exists_rat_abs_sub_le_and_den_le θ hn
  have hrpos : (0:ℝ) < r.den := by exact_mod_cast r.pos
  have hden' : (r.den:ℝ) ≤ n := by exact_mod_cast hden
  have hnX : (n:ℝ) ≤ X/Q := Nat.floor_le (by positivity)
  have hnlarge : X/Q < (n:ℝ)+1 := Nat.lt_floor_add_one (X/Q)
  have happrox : |θ-(r:ℝ)| ≤ Q/X := by
    refine herr.trans ?_
    calc
      _ ≤ 1/((n:ℝ)+1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have hr1 : (1:ℝ) ≤ r.den := by exact_mod_cast r.pos
        nlinarith
      _ ≤ 1/(X/Q) := one_div_le_one_div_of_le (by positivity) hnlarge.le
      _ = _ := by field_simp
  have hrlo : Q < (r.den:ℝ) := by
    by_contra h
    exact hminor ⟨r,le_of_not_gt h,happrox⟩
  refine ⟨r,hrlo,hden'.trans hnX,herr.trans ?_⟩
  apply one_div_le_one_div_of_le hX0
  have hscaled : X < Q*((n:ℝ)+1) := by
    simpa only [mul_comm] using (div_lt_iff₀ hQ).mp hnlarge
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NearbyAdditiveSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer a uniform partial-sum bound to a nearby frequency -/
namespace JointDickman
open Finset

lemma sum_positive_as_shifted {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, f n) = ∑ i ∈ range N, f (i+1) := by
  have hi : Ioc 0 N = Ico 1 (N+1) := by
    ext n
    simp only [mem_Ioc,mem_Ico]
    omega
  rw [hi]
  symm
  simpa only [Nat.zero_add,Nat.Ico_zero_eq_range] using sum_Ico_add' f 0 N 1

theorem nearby_additive_sum_bound (f : ℕ → ℂ) (N : ℕ) (θ φ T : ℝ)
    (hT : 0 ≤ T)
    (hf : ∀ k ≤ N, ‖∑ n ∈ Ioc 0 k, f n*additivePhase ((n:ℝ)*φ)‖ ≤ T) :
    ‖∑ n ∈ Ioc 0 N, f n*additivePhase ((n:ℝ)*θ)‖ ≤
      T*(1+2*Real.pi*N*|θ-φ|) := by
  let z := fun i : ℕ => f (i+1)*additivePhase (((i+1:ℕ):ℝ)*φ)
  let w := fun i : ℕ => additivePhase (((i+1:ℕ):ℝ)*(θ-φ))
  have hz (k : ℕ) (hk : k ≤ N) : ‖∑ i ∈ range k, z i‖ ≤ T := by
    simpa only [sum_positive_as_shifted] using hf k hk
  have hw (i : ℕ) (_hi : i < N) : ‖w i‖ ≤ 1 := (norm_additivePhase _).le
  have hd (i : ℕ) (_hi : i < N) : ‖w (i+1)-w i‖ ≤ 2*Real.pi*|θ-φ| := by
    apply (additivePhase_difference_norm_le _ _).trans_eq
    congr 2
    push_cast
    ring
  have he : (∑ n ∈ Ioc 0 N, f n*additivePhase ((n:ℝ)*θ)) =
      ∑ i ∈ range N, w i*z i := by
    rw [sum_positive_as_shifted]
    apply sum_congr rfl
    intro i hi
    dsimp [w,z]
    rw [show (((i+1:ℕ):ℝ)*θ) = (((i+1:ℕ):ℝ)*(θ-φ))+(((i+1:ℕ):ℝ)*φ) by ring,
      additivePhase_add]
    ring
  rw [he]
  have h := bounded_partial_sums_weighted z w N T 1 (2*Real.pi*|θ-φ|)
    hT zero_le_one (by positivity) hz hw hd
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RationalPartialSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform rational partial sums down to the trivial range -/
namespace JointDickman
open Finset

lemma bounded_real_additive_sum (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (N : ℕ) (θ : ℝ) :
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖(f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (1:ℝ) := by
      apply sum_le_sum
      intro n hn
      simpa only [norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs] using hf n
    _ = _ := by simp

theorem squarefree_rational_uniform_partial_sums : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B q : ℕ) (u : ℤ),
    0 < N → 2 ≤ B → (80:ℝ)*Real.log B ≤ B →
    (B:ℝ)/2 ≤ Real.log N → Real.log N ≤ 3*(B:ℝ) →
    0 < q → u.natAbs.Coprime q → (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^10 →
    ∀ M ≤ N, ‖∑ n ∈ Ioc 0 M, (f n:ℂ)*additivePhase ((n:ℝ)*((u:ℝ)/q))‖ ≤
      C*N*(1+Real.log B)/(B:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := squarefree_integer_rational_polylog_sum_bound_jd
  refine ⟨1+4*C,by positivity,?_⟩
  intro f hf hb hs N B q u hN hB hlogB hloglo hloghi hq hu hqlo hqhi M hMN
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hBR : (0:ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hB1 : (1:ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB1
  let T := (N:ℝ)*(1+Real.log B)/(B:ℝ)
  have hT : 0 ≤ T := by dsimp [T] <;> positivity
  by_cases hsmall : (M:ℝ) ≤ (N:ℝ)/(B:ℝ)^2
  · have htriv := bounded_real_additive_sum f hb M ((u:ℝ)/q)
    have hscale : (N:ℝ)/(B:ℝ)^2 ≤ T := by
      dsimp [T]
      apply (div_le_div_iff₀ (pow_pos hBR 2) hBR).mpr
      have hBB : (B:ℝ) ≤ (B:ℝ)^2 := le_self_pow₀ hB1 (by norm_num : 2 ≠ 0)
      nlinarith [mul_nonneg hlB (sq_nonneg (B:ℝ))]
    have hCT : T ≤ (1+4*C)*T := by nlinarith
    convert htriv.trans (hsmall.trans (hscale.trans hCT)) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [T]
    ring
  have hMlo : (N:ℝ)/(B:ℝ)^2 ≤ M := (lt_of_not_ge hsmall).le
  have hMR : (0:ℝ) < M := (div_pos hNR (pow_pos hBR 2)).trans_le hMlo
  have hlogM : (B:ℝ)/4 ≤ Real.log M := by
    have hh := Real.log_le_log (div_pos hNR (pow_pos hBR 2)) hMlo
    rw [Real.log_div hNR.ne' (pow_ne_zero 2 hBR.ne'),Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hBM : B^20 ≤ M := by
    have hpow : (0:ℝ) < (B:ℝ)^20 := pow_pos hBR 20
    have hlogpow : Real.log ((B:ℝ)^20) ≤ Real.log M := by
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith
    have he := (Real.log_le_log_iff hpow hMR).mp hlogpow
    exact_mod_cast he
  have hqM : (q:ℝ) ≤ (M:ℝ)/(B:ℝ)^8 := by
    calc
      _ ≤ (N:ℝ)/(B:ℝ)^10 := hqhi
      _ = ((N:ℝ)/(B:ℝ)^2)/(B:ℝ)^8 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hMlo (pow_nonneg hBR.le 8)
  have hlogMhi : Real.log M ≤ 3*(B:ℝ) :=
    (Real.log_le_log hMR (by exact_mod_cast hMN)).trans hloghi
  have h := hbound f hf hb hs M B q u hB hBM hq hu hlogMhi hqlo hqM
  have hmain : C*M*(1+Real.log B)/Real.log M ≤ 4*C*T := by
    calc
      _ ≤ C*N*(1+Real.log B)/((B:ℝ)/4) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hlogM
      _ = _ := by dsimp [T] <;> ring
  have hCT : 4*C*T ≤ (1+4*C)*T := by nlinarith
  convert h.trans (hmain.trans hCT) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [T]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeNearbySum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The needed Montgomery--Vaughan special case near a rational -/
namespace JointDickman
open Finset

theorem squarefree_near_rational_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B q : ℕ) (u : ℤ) (θ V : ℝ),
    0 < N → 2 ≤ B → (80:ℝ)*Real.log B ≤ B →
    (B:ℝ)/2 ≤ Real.log N → Real.log N ≤ 3*(B:ℝ) →
    0 < q → u.natAbs.Coprime q → (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^10 →
    (N:ℝ)*|θ-(u:ℝ)/q| ≤ V →
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ ≤
      C*(1+2*Real.pi*V)*N*(1+Real.log B)/(B:ℝ) := by
  obtain ⟨C,hC,hpartial⟩ := squarefree_rational_uniform_partial_sums
  refine ⟨C,hC,?_⟩
  intro f hf hb hs N B q u θ V hN hB hlogB hloglo hloghi hq hu hqlo hqhi hV
  let T := C*N*(1+Real.log B)/(B:ℝ)
  have hT : 0 ≤ T := by
    dsimp [T]
    have hlog : 0 ≤ Real.log B := Real.log_natCast_nonneg B
    positivity
  have h := nearby_additive_sum_bound (fun n => (f n:ℂ)) N θ ((u:ℝ)/q) T hT
    (hpartial f hf hb hs N B q u hN hB hlogB hloglo hloghi hq hu hqlo hqhi)
  apply h.trans
  calc
    _ ≤ T*(1+2*Real.pi*V) := by
      apply mul_le_mul_of_nonneg_left _ hT
      nlinarith [Real.pi_pos]
    _ = _ := by dsimp [T] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeMinorArc
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The squarefree exponential bound off the manuscript's rational arcs -/
namespace JointDickman
open Finset

theorem squarefree_minor_arc_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B : ℕ) (X θ V : ℝ),
    0 < N → 2 ≤ B → (80:ℝ)*Real.log B ≤ B →
    (B:ℝ)/2 ≤ Real.log N → Real.log N ≤ 3*(B:ℝ) →
    (B:ℝ)^12 ≤ X → X ≤ (N:ℝ)*(B:ℝ)^2 → (N:ℝ) ≤ V*X →
    ¬ InRationalArc θ ((B:ℝ)^12) ((B:ℝ)^13/X) →
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ ≤
      C*(1+2*Real.pi*V)*N*(1+Real.log B)/(B:ℝ) := by
  obtain ⟨C,hC,hnear⟩ := squarefree_near_rational_sum_bound
  refine ⟨C,hC,?_⟩
  intro f hf hb hs N B X θ V hN hB hlogB hloglo hloghi hX hXN hNV hminor
  have hB0 : (0:ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hB1 : (1:ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hX0 : 0 < X := (pow_pos hB0 12).trans_le hX
  have hm : ¬ InRationalArc θ ((B:ℝ)^12) ((B:ℝ)^12/X) := by
    rintro ⟨r,hr,he⟩
    apply hminor
    refine ⟨r,hr,he.trans ?_⟩
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hB1 (by norm_num : 12 ≤ 13)) hX0.le
  obtain ⟨r,hrlo,hrhi,herr⟩ := minorArc_strong_rational_approximation (pow_pos hB0 12) hX hm
  have hqN : (r.den:ℝ) ≤ (N:ℝ)/(B:ℝ)^10 := by
    apply hrhi.trans
    calc
      _ ≤ ((N:ℝ)*(B:ℝ)^2)/(B:ℝ)^12 := div_le_div_of_nonneg_right hXN (pow_nonneg hB0.le 12)
      _ = _ := by field_simp
  apply hnear f hf hb hs N B r.den r.num θ V hN hB hlogB hloglo hloghi
    r.pos r.reduced hrlo.le hqN
  have hh := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg N)
  have hv : (N:ℝ)/X ≤ V := (div_le_iff₀ hX0).mpr hNV
  have hh' : (N:ℝ)*|θ-(r:ℝ)| ≤ (N:ℝ)/X := by
    simpa only [mul_one_div] using hh
  simpa only [Rat.cast_def] using hh'.trans hv

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_DischargedCoefficientMinorArc
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient minor-arc estimate on the actual logarithmic range -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem coefficient_minorArc_bounded_log {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
    ∀ (Y : ℕ) (X θ V : ℝ), 0 < Y →
      (B:ℝ)/2 ≤ Real.log Y → Real.log Y ≤ 3*(B:ℝ) →
      (B:ℝ)^12 ≤ X → X ≤ (Y:ℝ)*(B:ℝ)^2 → (Y:ℝ) ≤ V*X →
      ¬ InRationalArc θ ((B:ℝ)^12) ((B:ℝ)^13/X) →
      ‖coefficientAdditivePartialSum B Y θ‖ ≤
        C*(1+2*Real.pi*V)*Y*(B:ℝ)^(-1/2+ε) := by
  obtain ⟨C,hC,hminor⟩ := squarefree_minor_arc_sum_bound
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [eventually_nat_log_linear 80,coefficientScale_power (half_pos hε),
    eventually_nat_one_add_log_power (half_pos hε),eventually_ge_atTop 2]
    with B hlinear hscale hlog hB
  intro Y X θ V hY hYlo hYhi hX hXY hYV hnot
  have hB0 : (0:ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hX0 : 0 < X := (pow_pos hB0 12).trans_le hX
  have hY0 : (0:ℝ) < Y := by exact_mod_cast hY
  have hV : 0 ≤ V := by nlinarith
  have hfactor : 0 ≤ 1+2*Real.pi*V := by positivity
  have hraw := hminor (roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1/2))
    (roughSquarefreeWeight_isMultiplicative _ _)
    (roughSquarefreeWeight_half_bounded _)
    (by intro n hn; simp [roughSquarefreeWeight,squarefreeWeight,hn])
    Y B X θ V hY hB hlinear hYlo hYhi hX hXY hYV hnot
  have hi : Ioc 0 Y = Icc 1 Y := by
    ext n
    simp only [mem_Ioc,mem_Icc]
    omega
  rw [hi] at hraw
  rw [coefficientAdditivePartialSum_factor,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (coefficientScale_nonneg B)]
  calc
    _ ≤ coefficientScale B*(C*(1+2*Real.pi*V)*Y*(1+Real.log B)/(B:ℝ)) :=
      mul_le_mul_of_nonneg_left hraw (coefficientScale_nonneg B)
    _ ≤ (B:ℝ)^(1/2+ε/2)*(C*(1+2*Real.pi*V)*Y*(2*(B:ℝ)^(ε/2))/(B:ℝ)) := by
      apply mul_le_mul hscale
      · gcongr
      · positivity
      · positivity
    _ = _ := by
      have hp : (B:ℝ)^(1/2+ε/2)*(B:ℝ)^(ε/2)/(B:ℝ) = (B:ℝ)^(-1/2+ε) := by
        calc
          _ = (B:ℝ)^((1/2+ε/2)+(ε/2))/(B:ℝ) := by rw [←Real.rpow_add hB0]
          _ = (B:ℝ)^((1/2+ε/2)+(ε/2))/(B:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
          _ = _ := by
            rw [←Real.rpow_sub hB0]
            congr 1
            ring
      calc
        _ = 2*C*(1+2*Real.pi*V)*Y*((B:ℝ)^(1/2+ε/2)*(B:ℝ)^(ε/2)/(B:ℝ)) := by ring
        _ = _ := by rw [hp]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DischargedSmoothMinorArc
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharged smooth minor arcs in the logarithmic range used by the main proof -/

namespace JointDickman
open Filter Finset
open scoped Topology

open Classical in
theorem smooth_coefficient_minorArc_bounded_log
    {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ X θ : ℝ, 0 < X →
      (9/10 : ℝ)*B ≤ Real.log X → Real.log X ≤ (11/5 : ℝ)*B →
      ¬ InRationalArc θ ((B : ℝ)^12) ((B : ℝ)^13/X) →
      ∀ (w w' : ℝ → ℝ) (M N : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) →
      (∀ t, t ≤ a ∨ b < t → w t = 0) →
      ‖smoothCoefficientAdditiveSum B X θ w‖ ≤
        C*b*(2*M+N*(b-a))*X*(B : ℝ)^(-1/2+ε) := by
  obtain ⟨C₀,hC₀,hbound⟩ := coefficient_minorArc_bounded_log hε
  have hb : 0 < b := ha.trans_le hab
  let C := C₀*(1+2*Real.pi*b)
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hlogb : ∀ᶠ B : ℕ in atTop, Real.log b ≤ (4/5:ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<4/5)).eventually_ge_atTop _
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,minorArc_support_window (b := b) ha,eventually_ge_atTop 1,hlogb]
    with B hboundB hwindow hB hlogbB
  intro X θ hX hlogX hlogXhi hminor w w' M N hM hN hw hw' hwbound hw'bound hsupport
  obtain ⟨hXlarge,hwindowX⟩ := hwindow X hX hlogX
  let D := C*b*X*(B : ℝ)^(-1/2+ε)
  have hpartial : ∀ t ∈ Set.Icc (a*X) (b*X),
      ‖∑ n ∈ Icc 0 ⌊t⌋₊, (coefficientWeight B n : ℂ)*additivePhase ((n : ℝ)*θ)‖ ≤ D := by
    intro t ht
    obtain ⟨hY,hlogY,hXY,hYb⟩ := hwindowX t ht
    rw [coefficient_partial_sum_from_zero]
    have hY0 : (0:ℝ) < ⌊t⌋₊ := by exact_mod_cast (show 0 < ⌊t⌋₊ by omega)
    have hlogYhi : Real.log (⌊t⌋₊:ℝ) ≤ 3*(B:ℝ) := by
      have hh := Real.log_le_log hY0 hYb
      rw [Real.log_mul hb.ne' hX.ne'] at hh
      linarith
    exact (hboundB ⌊t⌋₊ X θ b (by omega) hlogY hlogYhi hXlarge hXY hYb hminor).trans
      (by
        dsimp [D,C]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg B) _)
        nlinarith)
  have htest := complex_partial_summation_bound
    (fun n => (coefficientWeight B n : ℂ)*additivePhase ((n : ℝ)*θ))
    (scaledOscillatoryTest w 0 X) (scaledOscillatoryTestDeriv w w' 0 X)
    (a := a*X) (b := b*X) (D := D) (M := M) (N := N/X)
    (mul_nonneg ha.le hX.le) (mul_le_mul_of_nonneg_right hab hX.le)
    (by dsimp [D] <;> positivity) hM (div_nonneg hN hX.le)
    (fun t _ => hasDerivAt_scaledOscillatoryTest (hw (t/X)))
    (scaledOscillatoryTestDeriv_continuous (continuous_iff_continuousAt.mpr (fun t => (hw t).continuousAt)) hw' 0 X).continuousOn
    (fun t _ => scaledOscillatoryTest_norm_le (hwbound (t/X)))
    (fun t _ => by
      simpa using scaledOscillatoryTestDeriv_norm_le (ξ := 0) hX
        (hwbound (t/X)) (hw'bound (t/X))) hpartial
  have hsum := tsum_eq_Ioc_of_scaled_support ha.le hab hX hsupport
    (fun n => (coefficientWeight B n : ℂ)*(w (n/X) : ℂ)*additivePhase ((n : ℝ)*θ))
    (fun n hn => by simp [hn])
  have hsum' : smoothCoefficientAdditiveSum B X θ w =
      ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
        scaledOscillatoryTest w 0 X n *
          ((coefficientWeight B n : ℂ)*additivePhase ((n : ℝ)*θ)) := by
    rw [smoothCoefficientAdditiveSum,hsum]
    apply sum_congr rfl
    intro n _
    simp only [scaledOscillatoryTest,oscillatoryTest,zero_mul]
    have hzero : additivePhase 0 = 1 := by simp [additivePhase]
    rw [hzero,mul_one]
    ring
  rw [hsum']
  refine htest.trans_eq ?_
  dsimp [D]
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DischargedMinorArcBox
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual separated kernel has a power-saving minor-arc contribution -/

namespace JointDickman
open Filter Finset MeasureTheory
open scoped Topology

theorem minorArc_box_bound_bounded_log
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b c d ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ T X : ℝ, 0 < T → 0 < X →
      (9/10 : ℝ)*B ≤ Real.log X → Real.log X ≤ (11/5 : ℝ)*B →
      Real.log (T*X) ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) →
      ∀ j : ℕ, ∀ g h : Finset ℕ → ℝ,
      (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      (∀ S ⊆ auxiliaryPrimes B, |h S| ≤ 1) →
      ∀ (w₁ w₂ w₃ w₃' : ℝ → ℝ) (M M₃ N₃ : ℝ),
      0 ≤ M → 0 ≤ M₃ → 0 ≤ N₃ →
      (∀ t, |w₁ t| ≤ M) → (∀ t, |w₂ t| ≤ M) →
      (∀ t, HasDerivAt w₃ (w₃' t) t) → Continuous w₃' →
      (∀ t, |w₃ t| ≤ M₃) → (∀ t, |w₃' t| ≤ N₃) →
      (∀ t, t ≤ c ∨ d < t → w₃ t = 0) →
      ‖(B : ℂ)*(∫ θ in minorArcRegion B j X,
        endpointFourierSum B a b (T*X) g w₁ θ *
        endpointFourierSum B a b (T*X) h w₂ (-θ) *
        smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w₃)‖ ≤
      K*M^2*(2*M₃+N₃*(d-c))*(B : ℝ)^(-5/4+ε)/T := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hmom⟩ := endpoint_fourier_moments hSD hM hMP ha hab (half_pos hε)
  obtain ⟨C₃,hC₃,hminor⟩ := smooth_coefficient_minorArc_bounded_log hc hcd (half_pos hε)
  have hd : 0 < d := hc.trans_le hcd
  refine ⟨C₂*C₃*d,by positivity,?_⟩
  filter_upwards [hmom,hminor,eventually_gt_atTop 0] with B hmomB hminorB hB
  intro T X hT hX hlogX hlogXhi hlogTX j g h hg hh w₁ w₂ w₃ w₃' M M₃ N₃ hM0 hM₃ hN₃
    hw₁ hw₂ hw₃ hw₃' hbw₃ hbw₃' hsupp
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let Q := C₂*M^2*(B : ℝ)^(-7/4+ε/2)/(T*X)
  let D := C₃*d*(2*M₃+N₃*(d-c))*X*(B : ℝ)^(-1/2+ε/2)
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  have hF := (hmomB (T*X) (mul_pos hT hX) hlogTX.1 hlogTX.2 g hg w₁ M hM0 hw₁).2
  have hG : (∫ θ in (0 : ℝ)..1, ‖endpointFourierSum B a b (T*X) h w₂ (-θ)‖^2) ≤ Q := by
    simpa only [endpointFourierSum_neg_norm] using
      (hmomB (T*X) (mul_pos hT hX) hlogTX.1 hlogTX.2 h hh w₂ M hM0 hw₂).2
  have hint := discarded_region_integral_bound
    (H := fun θ => smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w₃)
    (minorArcRegion_measurable B j X) (minorArcRegion_subset B j X) hD
    (endpointFourierSum_continuous B a b (T*X) g w₁)
    ((endpointFourierSum_continuous B a b (T*X) h w₂).comp continuous_neg)
    (fun θ hθ => hminorB X (-(j : ℝ)*θ) hX hlogX hlogXhi hθ.2 w₃ w₃' M₃ N₃
      hM₃ hN₃ hw₃ hw₃' hbw₃ hbw₃' hsupp)
  rw [norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (B : ℝ)*(D/2*(Q+Q)) := mul_le_mul_of_nonneg_left
      (hint.trans (mul_le_mul_of_nonneg_left (add_le_add hF hG) (div_nonneg hD (by norm_num)))) hB0.le
    _ = _ := by
      have hp : (B : ℝ)^(-5/4+ε) =
          (B : ℝ)*(B : ℝ)^(-1/2+ε/2)*(B : ℝ)^(-7/4+ε/2) := by
        calc
          _ = (B : ℝ)^((1+(-1/2+ε/2))+(-7/4+ε/2)) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add hB0,Real.rpow_add hB0,Real.rpow_one]
      rw [hp]
      dsimp [D,Q]
      field_simp
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MajorArcPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measurable major-arc partition of the exact Fourier integral -/

namespace JointDickman
open Filter MeasureTheory Set Function
open scoped Topology

theorem majorArcRegion_eq_iUnion (B j : ℕ) (X : ℝ) :
    majorArcRegion B j X = ⋃ r : ℚ, rationalArcPiece B j X r := by
  ext θ
  simp only [majorArcRegion,rationalArcPiece,mem_ofPred_eq,mem_iUnion,InRationalArc]
  aesop

theorem rationalArcPiece_measurable (B j : ℕ) (X : ℝ) (r : ℚ) :
    MeasurableSet (rationalArcPiece B j X r) := by
  by_cases hr : (r.den : ℝ) ≤ (B : ℝ)^12
  · have hs : MeasurableSet {θ : ℝ | |-(j : ℝ)*θ-(r : ℝ)| ≤ (B : ℝ)^13/X} :=
      (isClosed_le ((continuous_const.mul continuous_id).sub continuous_const).abs
        continuous_const).measurableSet
    convert (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)).inter hs using 1
    all_goals try with_reducible_and_instances rfl
    ext θ
    simp [rationalArcPiece,hr]
  · simp [rationalArcPiece,hr]

theorem majorArcRegion_measurable (B j : ℕ) (X : ℝ) :
    MeasurableSet (majorArcRegion B j X) := by
  rw [majorArcRegion_eq_iUnion]
  exact MeasurableSet.iUnion (rationalArcPiece_measurable B j X)

theorem majorMinor_partition (B j : ℕ) (X : ℝ) :
    majorArcRegion B j X ∪ minorArcRegion B j X = Ioc 0 1 := by
  ext θ
  simp only [majorArcRegion,minorArcRegion,mem_union,mem_ofPred_eq]
  tauto

theorem majorMinor_disjoint (B j : ℕ) (X : ℝ) :
    Disjoint (majorArcRegion B j X) (minorArcRegion B j X) := by
  rw [disjoint_left]
  intro θ hmaj hmin
  exact hmin.2 hmaj.2

theorem majorMinor_integral (B j : ℕ) (X : ℝ) {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ θ in (0 : ℝ)..1, F θ) =
      (∫ θ in majorArcRegion B j X, F θ)+(∫ θ in minorArcRegion B j X, F θ) := by
  have hI : IntegrableOn F (Ioc 0 1) := (hF.intervalIntegrable 0 1).1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← majorMinor_partition B j X]
  exact setIntegral_union (majorMinor_disjoint B j X) (minorArcRegion_measurable B j X)
    (hI.mono_set (fun _ h => h.1)) (hI.mono_set (minorArcRegion_subset B j X))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArcCoefficientIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact coefficient phase on a lifted major arc -/

namespace JointDickman
open Finset

theorem additivePhase_int (k : ℤ) : additivePhase (k : ℝ) = 1 := by
  unfold additivePhase
  have he : ((2*Real.pi*(k : ℝ) : ℝ) : ℂ)*Complex.I =
      (k : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by push_cast <;> ring
  rw [he,Complex.exp_int_mul_two_pi_mul_I]

theorem additivePhase_add_int (x : ℝ) (k : ℤ) : additivePhase (x+k) = additivePhase x := by
  rw [additivePhase_add,additivePhase_int,mul_one]

theorem finiteAdditiveSum_add_int (s : Finset ℕ) (c : ℕ → ℂ) (θ : ℝ) (k : ℤ) :
    finiteAdditiveSum s c (θ+k) = finiteAdditiveSum s c θ := by
  unfold finiteAdditiveSum
  apply sum_congr rfl
  intro n _
  have he : (n : ℝ)*(θ+k) = n*θ+((n : ℤ)*k : ℤ) := by push_cast <;> ring
  rw [he,additivePhase_add_int]

theorem finiteAdditiveSum_periodic (s : Finset ℕ) (c : ℕ → ℂ) :
    Function.Periodic (finiteAdditiveSum s c) 1 := by
  intro θ
  simpa only [Int.cast_one] using finiteAdditiveSum_add_int s c θ 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDensityRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Lipschitz control of the coefficient density -/

namespace JointDickman
open Filter
open scoped Topology

theorem coefficientDensity_bounded_lipschitz
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    {δ : ℝ} (hδ : 0 < δ) (H : ℕ) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ ∀ᶠ B : ℕ in atTop,
      (∀ s : ℝ, δ ≤ s → |coefficientDensity c H B s| ≤ M) ∧
      (∀ s t : ℝ, δ ≤ s → δ ≤ t →
        |coefficientDensity c H B s-coefficientDensity c H B t| ≤ L*|s-t|) := by
  obtain ⟨M,hM0,L,hbound⟩ := scaledRoughDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1/2) hδ H
  let J : ℝ := (4 : ℝ)^(1/2 : ℝ)+1
  have hJ : 0 ≤ J := by dsimp [J] <;> positivity
  have hquot : ∀ᶠ B : ℕ in atTop,
      |coefficientScale B/(primeNormalizer (auxiliaryPrimes B) (1/2)*B)| ≤ J := by
    have hh := (roughMeanNormalization_quotient_tendsto hM
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)).abs
    have hpos := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (1/2 : ℝ)
    have he := hh.eventually (eventually_le_nhds (lt_add_one |(4 : ℝ)^(1/2 : ℝ)|))
    simpa only [← coefficientScale_eq_roughMeanNormalization,abs_of_pos hpos] using he
  refine ⟨J*M,J*(L : ℝ),mul_nonneg hJ hM0,mul_nonneg hJ L.coe_nonneg,?_⟩
  filter_upwards [hbound,hquot,eventually_gt_atTop 0] with B hboundB hquotB hB
  constructor
  · intro s hs
    rw [coefficientDensity_eq_scaled c H B hB (hδ.trans_le hs),abs_mul]
    exact mul_le_mul hquotB (hboundB.1 s hs) (abs_nonneg _) hJ
  · intro s t hs ht
    rw [coefficientDensity_eq_scaled c H B hB (hδ.trans_le hs),
      coefficientDensity_eq_scaled c H B hB (hδ.trans_le ht),← mul_sub,abs_mul]
    have hh := hboundB.2.dist_le_mul s hs t ht
    rw [Real.dist_eq,Real.dist_eq] at hh
    calc
      _ ≤ J*((L : ℝ)*|s-t|) := mul_le_mul hquotB hh (abs_nonneg _) hJ
      _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RescaledMajorIntegral
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact rescaled frequency integral on all major arcs -/

namespace JointDickman
open Filter MeasureTheory Function Finset
open scoped Topology

theorem smoothCoefficientAdditiveSum_continuous (B : ℕ) {a b X : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hX : 0 < X) {w : ℝ → ℝ}
    (hsupp : ∀ s, s ≤ a ∨ b < s → w s = 0) :
    Continuous (fun θ => smoothCoefficientAdditiveSum B X θ w) := by
  have heq : (fun θ => smoothCoefficientAdditiveSum B X θ w) =
      fun θ => ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
        (coefficientWeight B n : ℂ)*(w (n/X) : ℂ)*additivePhase ((n : ℝ)*θ) := by
    funext θ
    exact tsum_eq_Ioc_of_scaled_support ha hab hX hsupp _ (by intro n hn; simp [hn])
  rw [heq]
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_id))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TruncatedMajorRegion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutting the major arcs at a finite denominator -/

namespace JointDickman
open Filter MeasureTheory Set Function
open scoped Topology

theorem smallMajorArcRegion_measurable (B j : ℕ) (X : ℝ) (Q : ℕ) :
    MeasurableSet (smallMajorArcRegion B j X Q) := by
  apply MeasurableSet.iUnion
  intro r
  split_ifs
  · exact rationalArcPiece_measurable B j X r
  · exact MeasurableSet.empty

theorem largeMajorArcRegion_measurable (B j : ℕ) (X : ℝ) (Q : ℕ) :
    MeasurableSet (largeMajorArcRegion B j X Q) :=
  (majorArcRegion_measurable B j X).diff (smallMajorArcRegion_measurable B j X Q)

theorem smallMajorArcRegion_subset (B j : ℕ) (X : ℝ) (Q : ℕ) :
    smallMajorArcRegion B j X Q ⊆ majorArcRegion B j X := by
  intro x hx
  obtain ⟨r,hr⟩ := mem_iUnion.mp hx
  split_ifs at hr with hq
  · exact ⟨hr.1,r,hr.2.1,hr.2.2⟩
  · exact hr.elim

theorem majorArc_truncated_integral (B j Q : ℕ) (X : ℝ)
    {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ x in majorArcRegion B j X, F x) =
      (∫ x in smallMajorArcRegion B j X Q, F x)+
        (∫ x in largeMajorArcRegion B j X Q, F x) := by
  have hI : IntegrableOn F (majorArcRegion B j X) :=
    (hF.intervalIntegrable 0 1).1.mono_set (fun _ hx => hx.1)
  have hsmall := smallMajorArcRegion_subset B j X Q
  have heq : majorArcRegion B j X =
      smallMajorArcRegion B j X Q ∪ largeMajorArcRegion B j X Q := by
    exact (union_sdiff_cancel hsmall).symm
  rw [heq]
  apply setIntegral_union
  · exact disjoint_sdiff_right
  · exact largeMajorArcRegion_measurable B j X Q
  · exact hI.mono_set hsmall
  · exact hI.mono_set sdiff_subset

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointFullArcLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full-arc coefficient law with the actual endpoint sums -/

namespace JointDickman
open Finset Filter MeasureTheory Function
open scoped Topology SchwartzMap ArithmeticFunction.Moebius

theorem endpointFourierSum_periodic (B : ℕ) (a b N : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) :
    Periodic (endpointFourierSum B a b N g w) 1 := finiteAdditiveSum_periodic _ _

theorem endpointFourierSum_negative_periodic (B : ℕ) (a b N : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) :
    Periodic (fun θ => endpointFourierSum B a b N g w (-θ)) 1 := by
  intro θ
  change finiteAdditiveSum _ _ (-(θ+1)) = finiteAdditiveSum _ _ (-θ)
  have he : -(θ+1) = -θ+((-1 : ℤ) : ℝ) := by push_cast <;> ring
  rw [he,finiteAdditiveSum_add_int]

theorem endpoint_fullArc_coefficient_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K C C₁ C₂ : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ᶠ B : ℕ in atTop, ∀ T X : ℝ, 0 < T → 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      Real.log (T*X) ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) →
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) (M M₀ D₀ : ℝ),
      0 ≤ M → 0 ≤ M₀ → 0 ≤ D₀ →
      (∀ x, |w₁ x| ≤ M) → (∀ x, |w₂ x| ≤ M) →
      (∀ x, HasDerivAt w (w' x) x) → Continuous w' →
      (∀ x, |w x| ≤ M₀) → (∀ x, |w' x| ≤ D₀) →
      (∀ x, x ≤ l ∨ u < x → w x = 0) →
      let F := endpointFourierSum B a b (T*X) (subsetSiteTest (auxiliaryPrimes B) g) w₁
      let G := fun θ => endpointFourierSum B a b (T*X) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ)
      ‖(∫ θ in smallMajorArcRegion B j X Q,
          F θ*G θ*smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w)-
        fullSmallMajorArcModel B j X Q (fun θ => F θ*G θ)
          (fun ξ => (coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ)
          (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))‖ ≤
        (X*((K*u*(2*M₀+(D₀+2*Real.pi*M₀)*(u-l)))*(B : ℝ)^(-50 : ℝ)+C*M₀/B))*
          (C₂*M^2*(B : ℝ)^(-(3/2 : ℝ))/(T*X))+
        ((B^12 : ℕ) : ℝ)*((B^12 : ℕ)+1)*
          (((C₁*M/B)^2)*(((B : ℝ)^13)^10)⁻¹*|coefficientDensity c H B (Real.log X/B)| *
            (∫ ξ : ℝ, |ξ|^10*‖testFourierTransform w ξ‖)) := by
  obtain ⟨c,hc,hcpos,H,K,hK,he⟩ := coefficient_frozen_fullArc_integral_law_jd hSD hSW hM hMP
  obtain ⟨C,hC,hcoef⟩ := he l u hl hlu
  obtain ⟨C₁,C₂,hC₁,hC₂,hmom⟩ := endpoint_fourier_moments hSD hM hMP ha hab
    (by norm_num : (0 : ℝ) < 1/4)
  refine ⟨c,hc,hcpos,H,K,C,C₁,C₂,hK,hC,hC₁,hC₂,?_⟩
  filter_upwards [hcoef,hmom,eventually_ge_atTop 1] with B hcB hmB hB
  intro T X hT hX hlogX hlogN j _ Q g h hg hh w₁ w₂ w w' M M₀ D₀ hM0 hM₀ hD₀
    hw₁ hw₂ hw hw' hwb hwd hsupp
  dsimp only
  let F := endpointFourierSum B a b (T*X) (subsetSiteTest (auxiliaryPrimes B) g) w₁
  let G := fun θ => endpointFourierSum B a b (T*X) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ)
  have hf := hmB (T*X) (mul_pos hT hX) hlogN.1 hlogN.2 (subsetSiteTest (auxiliaryPrimes B) g) (fun _ _ => hg _) w₁ M hM0 hw₁
  have hh' := hmB (T*X) (mul_pos hT hX) hlogN.1 hlogN.2 (subsetSiteTest (auxiliaryPrimes B) h) (fun _ _ => hh _) w₂ M hM0 hw₂
  norm_num only [show (-7/4+(1/4 : ℝ)) = -3/2 by norm_num] at hf hh'
  have hGint : (∫ θ in (0 : ℝ)..1, ‖G θ‖^2) ≤ C₂*M^2*(B : ℝ)^(-(3/2 : ℝ))/(T*X) := by
    simpa only [G,endpointFourierSum_neg_norm] using hh'.2
  have hFb : ∀ θ, ‖F θ‖ ≤ C₁*M/B := hf.1
  have hGb : ∀ θ, ‖G θ‖ ≤ C₁*M/B := fun θ => hh'.1 (-θ)
  have hF : Continuous F := endpointFourierSum_continuous _ _ _ _ _ _
  have hG : Continuous G := (endpointFourierSum_continuous _ _ _ _ _ _).comp continuous_neg
  have hP : 0 ≤ X*((K*u*(2*M₀+(D₀+2*Real.pi*M₀)*(u-l)))*(B : ℝ)^(-50 : ℝ)+C*M₀/B) := by
    have hu := hl.trans_le hlu
    positivity
  have he' := hcB X hX hlogX j inferInstance Q w w' M₀ D₀ hM₀ hD₀ hw hw' hwb hwd hsupp
    F G hF hG (endpointFourierSum_periodic _ _ _ _ _ _) (endpointFourierSum_negative_periodic _ _ _ _ _ _)
    (C₁*M/B) (C₁*M/B) (by positivity) (by positivity) hFb hGb
  refine he'.trans ?_
  apply add_le_add
  · exact (mul_le_mul_of_nonneg_left (add_le_add hf.2 hGint) (div_nonneg hP (by norm_num))).trans_eq (by ring)
  · exact le_of_eq (by ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HistogramWindowOverlap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded overlap of logarithmic windows along a geometric scale -/

namespace JointDickman
open Finset

/-- The integer lattice has at most length+1 points in any real interval. -/
theorem integer_interval_card_le (S : Finset ℤ) {a b : ℝ} (hab : a ≤ b)
    (hS : ∀ m ∈ S, a ≤ (m : ℝ) ∧ (m : ℝ) ≤ b) :
    (S.card : ℝ) ≤ b-a+1 := by
  classical
  by_cases hne : S.Nonempty
  · let lo := S.min' hne
    let hi := S.max' hne
    have hlo : lo ∈ S := min'_mem S hne
    have hhi : hi ∈ S := max'_mem S hne
    have hord : lo ≤ hi := min'_le S hi hhi
    have hc : S.card ≤ (hi-lo+1).toNat := by
      have hs : S ⊆ Icc lo hi := fun m hm => mem_Icc.mpr ⟨min'_le S m hm,le_max' S m hm⟩
      have he : hi+1-lo = hi-lo+1 := by ring
      simpa only [Int.card_Icc,he] using card_le_card hs
    have hz : 0 ≤ hi-lo+1 := by omega
    have hcast : (S.card : ℝ) ≤ (hi : ℝ)-(lo : ℝ)+1 := by
      have hh : (S.card : ℤ) ≤ hi-lo+1 := by
        have hh := Int.ofNat_le.mpr hc
        simpa only [Int.toNat_of_nonneg hz] using hh
      exact_mod_cast hh
    exact hcast.trans (by linarith [(hS lo hlo).1,(hS hi hhi).2])
  · have he := not_nonempty_iff_eq_empty.mp hne
    simp only [he,card_empty,Nat.cast_zero]
    linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeometricBoxErrors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing per-box power savings over the manuscript's geometric scale -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem geometric_box_count {B : ℕ} (hB : 1 ≤ B) {t : ℝ} (ht : 0 < t)
    (S : Finset ℤ)
    (hS : ∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) :
    (S.card : ℝ) ≤ (8/(5*t)+1)*(B : ℝ) := by
  have hcount := integer_interval_card_le S
    (div_le_div_of_nonneg_right (by nlinarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B] : (9/10 : ℝ)*B ≤ (5/2 : ℝ)*B) ht.le)
    (by
      intro k hk
      exact ⟨(div_le_iff₀ ht).mpr (hS k hk).1,(le_div_iff₀ ht).mpr (hS k hk).2⟩)
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  refine hcount.trans ?_
  have he : ((5/2 : ℝ)*B)/t-((9/10 : ℝ)*B)/t = (8/(5*t))*(B : ℝ) := by ring
  rw [he]
  nlinarith

theorem geometric_box_error_sum {B : ℕ} (hB : 1 ≤ B) {t : ℝ} (ht : 0 < t)
    (S : Finset ℤ)
    (hS : ∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B))
    (E : ℤ → ℂ) {T C r : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hE : ∀ k ∈ S, T*‖E k‖ ≤ C*(B : ℝ)^r) :
    T*‖∑ k ∈ S, E k‖ ≤ ((8/(5*t)+1)*C)*(B : ℝ)^(r+1) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  calc
    _ ≤ T*∑ k ∈ S, ‖E k‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hT
    _ = ∑ k ∈ S, T*‖E k‖ := mul_sum _ _ _
    _ ≤ ∑ _k ∈ S, C*(B : ℝ)^r := sum_le_sum hE
    _ = (S.card : ℝ)*(C*(B : ℝ)^r) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ((8/(5*t)+1)*(B : ℝ))*(C*(B : ℝ)^r) :=
      mul_le_mul_of_nonneg_right (geometric_box_count hB ht S hS) (by positivity)
    _ = _ := by rw [Real.rpow_add hBr,Real.rpow_one]; ring

theorem geometric_box_error_vanishing {t r C : ℝ} (_ht : 0 < t) (hr : r < -1) :
    Tendsto (fun B : ℕ => ((8/(5*t)+1)*C)*(B : ℝ)^(r+1)) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_neg_atTop (by linarith : 0 < -(r+1))).comp
    tendsto_natCast_atTop_atTop).const_mul ((8/(5*t)+1)*C)
  simpa only [neg_neg,mul_zero,Function.comp_def] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientArcErrorScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing the actual frozen-coefficient error before summing boxes -/

namespace JointDickman

theorem coefficient_arc_error_scale {B T X η A C D F G E : ℝ}
    (hB : 1 ≤ B) (hT : 0 < T) (hX : 0 < X) (hη : 0 < η) (hscale : η*T ≤ B)
    (hA : 0 ≤ A) (_hC : 0 ≤ C) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hE : E ≤ X*(A*B^(-50 : ℝ)+C/B)*(D*B^(-(3/2 : ℝ))/(T*X))+
      B^12*(B^12+1)*((F/B)^2*((B^13)^10)⁻¹*G)) :
    T*B*E ≤ (D*(A+C)+2*F^2*G/η)*B^(-(3/2 : ℝ)) := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBne := hBpos.ne'
  have hTB : T ≤ B/η := (le_div_iff₀ hη).mpr (by nlinarith [hscale])
  have hp50 : B*B^(-50 : ℝ) ≤ 1 := by
    have he : B*B^(-50 : ℝ) = B^(-49 : ℝ) := by
      calc
        _ = B^(1 : ℝ)*B^(-50 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hBpos]; norm_num
    rw [he]
    exact Real.rpow_le_one_of_one_le_of_nonpos hB (by norm_num)
  have hmain : T*B*(X*(A*B^(-50 : ℝ)+C/B)*(D*B^(-(3/2 : ℝ))/(T*X))) ≤
      D*(A+C)*B^(-(3/2 : ℝ)) := by
    calc
      _ = D*(A*(B*B^(-50 : ℝ))+C)*B^(-(3/2 : ℝ)) := by field_simp
      _ ≤ _ := by
        gcongr
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hp50 hA
  have hnum : B^12*(B^12+1) ≤ 2*B^24 := by
    have hone : 1 ≤ B^12 := one_le_pow₀ hB
    have hp : B^12*B^12 = B^24 := by ring
    nlinarith
  have hden : ((B^13)^10)⁻¹ ≤ (B^28)⁻¹ := by
    apply inv_anti₀ (by positivity)
    rw [← pow_mul]
    exact pow_le_pow_right₀ hB (by norm_num : 28 ≤ 13*10)
  have hfrac : (F/B)^2 ≤ F^2 := pow_le_pow_left₀ (by positivity) (div_le_self hF hB) 2
  have htail : B^12*(B^12+1)*((F/B)^2*((B^13)^10)⁻¹*G) ≤ 2*F^2*G/B^4 := by
    calc
      _ ≤ (2*B^24)*(F^2*(B^28)⁻¹*G) := by gcongr
      _ = _ := by field_simp
  have hp2 : B^(-2 : ℝ) ≤ B^(-(3/2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
  have htail' : T*B*(B^12*(B^12+1)*((F/B)^2*((B^13)^10)⁻¹*G)) ≤
      (2*F^2*G/η)*B^(-(3/2 : ℝ)) := by
    calc
      _ ≤ (B/η)*B*(2*F^2*G/B^4) := by gcongr
      _ = (2*F^2*G/η)*B^(-2 : ℝ) := by
        rw [Real.rpow_neg hBpos.le,Real.rpow_ofNat]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hp2 (by positivity)
  calc
    _ ≤ T*B*(X*(A*B^(-50 : ℝ)+C/B)*(D*B^(-(3/2 : ℝ))/(T*X))+
        B^12*(B^12+1)*((F/B)^2*((B^13)^10)⁻¹*G)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = T*B*(X*(A*B^(-50 : ℝ)+C/B)*(D*B^(-(3/2 : ℝ))/(T*X)))+
        T*B*(B^12*(B^12+1)*((F/B)^2*((B^13)^10)⁻¹*G)) := mul_add _ _ _
    _ ≤ D*(A+C)*B^(-(3/2 : ℝ))+(2*F^2*G/η)*B^(-(3/2 : ℝ)) := add_le_add hmain htail'
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FullModelLinearity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linearity in the scalar weight of each geometric box -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

 theorem fullSmallMajorArcModel_mul (B j : ℕ) [NeZero j] (X : ℝ) (Q : ℕ)
    (F W : ℝ → ℂ) (a : ℕ+ → ℂ) (r : ℂ) :
    fullSmallMajorArcModel B j X Q F (fun ξ => r*W ξ) a =
      r*fullSmallMajorArcModel B j X Q F W a := by
  classical
  unfold fullSmallMajorArcModel
  have hi (q : ℕ+) (h : ZMod (j*(q : ℕ))) :
      (∫ ξ : ℝ, F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*(r*W ξ)) =
      r*∫ ξ : ℝ, F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by ring)
  simp_rw [hi]
  rw [mul_left_comm r]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro q _
  split_ifs
  · rw [mul_sum]
    apply sum_congr rfl
    intro h _
    split_ifs <;> ring
  · ring

theorem weightedGeometricSmallArcSum_sub_model (B j Q : ℕ) [NeZero j] (a b T t : ℝ)
    (S : Finset ℤ) (r d : ℤ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) :
    weightedGeometricSmallArcSum B j Q a b T t S r g h w₁ w₂ w-
      geometricFullArcSum B j Q a b T t S (fun k => r k*d k) g h w₁ w₂ w =
      ∑ k ∈ S, (r k : ℂ)*((B : ℂ)*
        ((∫ θ in smallMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
          geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ)-
        fullSmallMajorArcModel B j (Real.exp ((k : ℝ)*t)/T) Q
          (fun θ => endpointFourierSum B a b (Real.exp ((k : ℝ)*t))
              (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
            endpointFourierSum B a b (Real.exp ((k : ℝ)*t))
              (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ))
          (fun ξ => (d k : ℂ)*testFourierTransform w ξ)
          (fun q => (ArithmeticFunction.moebius (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ)))) := by
  unfold weightedGeometricSmallArcSum geometricFullArcSum
  simp only [Complex.ofReal_mul,← mul_assoc,fullSmallMajorArcModel_mul]
  rw [← mul_sub,← sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro k _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedBoxErrors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform geometric error bounds with bounded scalar box weights -/

namespace JointDickman
open Finset

theorem geometric_weighted_box_error_sum {B : ℕ} (hB : 1 ≤ B) {t : ℝ} (ht : 0 < t)
    (S : Finset ℤ)
    (hS : ∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B))
    (E r : ℤ → ℂ) {T C R p : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hr : ∀ k ∈ S, ‖r k‖ ≤ R) (hE : ∀ k ∈ S, T*‖E k‖ ≤ C*(B : ℝ)^p) :
    T*‖∑ k ∈ S, r k*E k‖ ≤ ((8/(5*t)+1)*(R*C))*(B : ℝ)^(p+1) := by
  apply geometric_box_error_sum hB ht S hS (fun k => r k*E k) hT (mul_nonneg hR hC)
  intro k hk
  rw [norm_mul]
  calc
    _ = ‖r k‖*(T*‖E k‖) := by ring
    _ ≤ R*(C*(B : ℝ)^p) := mul_le_mul (hr k hk) (hE k hk) (by positivity) hR
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedDiscardedArcs
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discarded arcs with the varying smooth box weights -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

theorem weighted_geometric_discarded_arcs_vanishing
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u) (ht : 0 < t)
    (w₁ w₂ w₃ w₃' : ℝ → ℝ) {M M₃ N₃ R : ℝ}
    (hR : 0 ≤ R)
    (hM0 : 0 ≤ M) (hM₃ : 0 ≤ M₃) (hN₃ : 0 ≤ N₃)
    (hw₁ : ∀ x, |w₁ x| ≤ M) (hw₂ : ∀ x, |w₂ x| ≤ M)
    (hw₃ : ∀ x, HasDerivAt w₃ (w₃' x) x) (hw₃' : Continuous w₃')
    (hwb₃ : ∀ x, |w₃ x| ≤ M₃) (hwd₃ : ∀ x, |w₃' x| ≤ N₃)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w₃ x = 0) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℝ, 0 < T → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
      ∀ Q : ℕ, (B : ℝ)^(2/5 : ℝ) ≤ Q → ∀ j : ℕ,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*‖(B : ℂ)*∑ k ∈ S, (r k : ℂ)*
        ((∫ θ in minorArcRegion B j (Real.exp ((k : ℝ)*t)/T),
            geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ)+
          (∫ θ in largeMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
            geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ))‖ ≤ ε B := by
  obtain ⟨C₁,hC₁,hminor⟩ := minorArc_box_bound_bounded_log hSD hM hMP ha hab hl hlu
    (by norm_num : (0 : ℝ) < 1/20)
  obtain ⟨C₂,D,K,hC₂,hD,hK,hmajor⟩ := largeMajorArc_box_bound_jd hSD hSW hM hMP ha hab hl hlu
    (by norm_num : (0 : ℝ) < 1/20)
  let A := C₁*M^2*(2*M₃+N₃*(u-l))
  let C := C₂*M^2*(D*M₃*(u-l)+K*u*(2*M₃+(N₃+2*Real.pi*M₃)*(u-l)))
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hC : 0 ≤ C := by dsimp [C]; have hu := hl.trans_le hlu; positivity
  let ε₁ := fun B : ℕ => ((8/(5*t)+1)*(R*A))*(B : ℝ)^((-(6/5 : ℝ))+1)
  let ε₂ := fun B : ℕ => ((8/(5*t)+1)*(R*C))*(B : ℝ)^((-(11/10 : ℝ))+1)
  refine ⟨fun B => ε₁ B+ε₂ B,?_,?_⟩
  · simpa using (geometric_box_error_vanishing (C := R*A) (r := -(6/5 : ℝ)) ht (by norm_num)).add
      (geometric_box_error_vanishing (C := R*C) (r := -(11/10 : ℝ)) ht (by norm_num))
  filter_upwards [hminor,hmajor,eventually_ge_atTop 1] with B hmin hmaj hB
  intro T hT S hbox hlog r hr Q hQ j g h hg hh
  have hN (k : ℤ) : T*(Real.exp ((k : ℝ)*t)/T) = Real.exp ((k : ℝ)*t) := by field_simp
  have hNlog (k : ℤ) (hk : k ∈ S) : Real.log (T*(Real.exp ((k : ℝ)*t)/T)) ∈
      Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) := by rw [hN,Real.log_exp]; exact hbox k hk
  let E₁ := fun k : ℤ => (B : ℂ)*(∫ θ in minorArcRegion B j (Real.exp ((k : ℝ)*t)/T),
    geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ)
  let E₂ := fun k : ℤ => (B : ℂ)*(∫ θ in largeMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
    geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ)
  have he₁ : ∀ k ∈ S, T*‖E₁ k‖ ≤ A*(B : ℝ)^(-(6/5 : ℝ)) := by
    intro k hk
    have he := hmin T (Real.exp ((k : ℝ)*t)/T) hT (div_pos (Real.exp_pos _) hT)
      (hlog k hk).1 (hlog k hk).2 (hNlog k hk) j (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h) (fun _ _ => hg _) (fun _ _ => hh _)
      w₁ w₂ w₃ w₃' M M₃ N₃ hM0 hM₃ hN₃ hw₁ hw₂ hw₃ hw₃' hwb₃ hwd₃ hsupp
    rw [hN] at he
    norm_num only [show (-5/4+(1/20 : ℝ)) = -6/5 by norm_num] at he
    simpa only [E₁,E₂,geometricBoxIntegrand,A,C,mul_comm T] using (le_div_iff₀ hT).mp he
  have he₂ : ∀ k ∈ S, T*‖E₂ k‖ ≤ C*(B : ℝ)^(-(11/10 : ℝ)) := by
    intro k hk
    have he := hmaj T (Real.exp ((k : ℝ)*t)/T) hT (div_pos (Real.exp_pos _) hT)
      (hlog k hk) (hNlog k hk) Q hQ j (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h) (fun _ _ => hg _) (fun _ _ => hh _)
      w₁ w₂ w₃ w₃' M M₃ N₃ hM0 hM₃ hN₃ hw₁ hw₂ hw₃ hw₃' hwb₃ hwd₃ hsupp
    rw [hN] at he
    norm_num only [show (-23/20+(1/20 : ℝ)) = -11/10 by norm_num] at he
    simpa only [E₁,E₂,geometricBoxIntegrand,A,C,mul_comm T] using (le_div_iff₀ hT).mp he
  have hr' : ∀ k ∈ S, ‖(r k : ℂ)‖ ≤ R := by
    intro k hk
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hr k hk
  have hsum₁ := geometric_weighted_box_error_sum hB ht S hbox E₁ (fun k => (r k : ℂ))
    hT.le hA hR hr' he₁
  have hsum₂ := geometric_weighted_box_error_sum hB ht S hbox E₂ (fun k => (r k : ℂ))
    hT.le hC hR hr' he₂
  have heq : (B : ℂ)*∑ k ∈ S, (r k : ℂ)*
      ((∫ θ in minorArcRegion B j (Real.exp ((k : ℝ)*t)/T),
          geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ)+
        (∫ θ in largeMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
          geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ)) =
      (∑ k ∈ S, (r k : ℂ)*E₁ k)+(∑ k ∈ S, (r k : ℂ)*E₂ k) := by
    simp only [mul_sum,mul_add,sum_add_distrib,E₁,E₂]
    congr 1 <;> apply sum_congr rfl <;> intro k _ <;> ring
  rw [heq]
  exact ((mul_le_mul_of_nonneg_left (norm_add_le _ _) hT.le).trans_eq (mul_add _ _ _)).trans
    (add_le_add hsum₁ hsum₂)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_WeightedGeometricCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient replacement with bounded weights on the geometric boxes -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology SchwartzMap ArithmeticFunction.Moebius

theorem weighted_geometric_coefficient_law_vanishing
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) {M M₀ D₀ R : ℝ}
    (hR : 0 ≤ R)
    (hM0 : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hD₀ : 0 ≤ D₀)
    (hw₁ : ∀ x, |w₁ x| ≤ M) (hw₂ : ∀ x, |w₂ x| ≤ M)
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : Continuous w')
    (hwb : ∀ x, |w x| ≤ M₀) (hwd : ∀ x, |w' x| ≤ D₀)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℝ, 0 < T → η*T ≤ B → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      T*‖weightedGeometricSmallArcSum B j Q a b T t S r g h w₁ w₂ w-
        geometricFullArcSum B j Q a b T t S (fun k => r k*d k) g h w₁ w₂ w‖ ≤ ε B := by
  obtain ⟨c,hc,hcpos,H,K,C,C₁,C₂,hK,hC,hC₁,hC₂,he⟩ :=
    endpoint_fullArc_coefficient_law hSD hSW hM hMP ha hab hl hlu
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  let A := K*u*(2*M₀+(D₀+2*Real.pi*M₀)*(u-l))
  let G := D*(∫ ξ : ℝ, |ξ|^10*‖testFourierTransform w ξ‖)
  let Cerror := (C₂*M^2)*(A+C*M₀)+2*(C₁*M)^2*G/η
  have hA : 0 ≤ A := by dsimp [A]; have hu := hl.trans_le hlu; positivity
  have hG : 0 ≤ G := by dsimp [G] <;> positivity
  have hCerror : 0 ≤ Cerror := by dsimp [Cerror] <;> positivity
  let ε := fun B : ℕ => ((8/(5*t)+1)*(R*Cerror))*(B : ℝ)^((-(3/2 : ℝ))+1)
  refine ⟨c,hc,hcpos,H,ε,geometric_box_error_vanishing ht (by norm_num),?_⟩
  filter_upwards [he,hden,eventually_ge_atTop 1] with B heB hdenB hB
  intro T hT hscale S hbox hlog r hr j _ Q g h hg hh
  dsimp only
  let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
  let I := fun k : ℤ => ∫ θ in smallMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
    geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ
  let P := fun k : ℤ => fullSmallMajorArcModel B j (Real.exp ((k : ℝ)*t)/T) Q
    (fun θ => endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
      endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ))
    (fun ξ => (d k : ℂ)*testFourierTransform w ξ) (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))
  let E := fun k : ℤ => (B : ℂ)*(I k-P k)
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hBr
  have hN (k : ℤ) : T*(Real.exp ((k : ℝ)*t)/T) = Real.exp ((k : ℝ)*t) := by field_simp
  have hlocal : ∀ k ∈ S, T*‖E k‖ ≤ Cerror*(B : ℝ)^(-(3/2 : ℝ)) := by
    intro k hk
    have hdk : |d k| ≤ D := by
      apply hdenB.1
      apply (le_div_iff₀ hBpos).mpr
      nlinarith [(hlog k hk).1]
    have hNk : Real.log (T*(Real.exp ((k : ℝ)*t)/T)) ∈
        Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) := by
      rw [hN,Real.log_exp]
      exact hbox k hk
    have hh := heB T (Real.exp ((k : ℝ)*t)/T) hT (div_pos (Real.exp_pos _) hT)
      (hlog k hk) hNk j Q g h hg hh w₁ w₂ w w' M M₀ D₀ hM0 hM₀ hD₀ hw₁ hw₂ hw hw' hwb hwd hsupp
    simp only [hN,Nat.cast_pow] at hh
    have hraw : ‖I k-P k‖ ≤ (Real.exp ((k : ℝ)*t)/T)*
        (A*(B : ℝ)^(-50 : ℝ)+(C*M₀)/B)*((C₂*M^2)*(B : ℝ)^(-(3/2 : ℝ))/(T*(Real.exp ((k : ℝ)*t)/T)))+
        (B : ℝ)^12*((B : ℝ)^12+1)*((C₁*M/B)^2*(((B : ℝ)^13)^10)⁻¹*G) := by
      rw [hN]
      refine hh.trans ?_
      apply add_le_add le_rfl
      have hmul := mul_le_mul_of_nonneg_left hdk (show 0 ≤
        (B : ℝ)^12*((B : ℝ)^12+1)*(C₁*M/B)^2*(((B : ℝ)^13)^10)⁻¹*
          (∫ ξ : ℝ, |ξ|^10*‖testFourierTransform w ξ‖) by positivity)
      convert hmul using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [d,G] <;> ring)
    have hh' := coefficient_arc_error_scale hBr hT (div_pos (Real.exp_pos _) hT) hη hscale
      hA (mul_nonneg hC hM₀) (mul_nonneg hC₂ (sq_nonneg M)) (mul_nonneg hC₁ hM0) hG hraw
    simpa only [E,norm_mul,Complex.norm_natCast,mul_assoc,Cerror] using hh'
  have hweighted : ∀ k ∈ S, T*‖(r k : ℂ)*E k‖ ≤ (R*Cerror)*(B : ℝ)^(-(3/2 : ℝ)) := by
    intro k hk
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ = |r k| *(T*‖E k‖) := by ring
      _ ≤ R*(Cerror*(B : ℝ)^(-(3/2 : ℝ))) :=
        mul_le_mul (hr k hk) (hlocal k hk) (by positivity) hR
      _ = _ := by ring
  have hsum := geometric_box_error_sum hB ht S hbox (fun k => (r k : ℂ)*E k)
    hT.le (mul_nonneg hR hCerror) hweighted
  rw [weightedGeometricSmallArcSum_sub_model]
  exact hsum

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedPeriodLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original separated Fourier expression and the retained full-arc model -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology SchwartzMap

theorem weighted_geometric_period_split (B j Q : ℕ) {a b T t l u : ℝ} (hT : 0 < T)
    (S : Finset ℤ) (r : ℤ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ w : ℝ → ℝ)
    (hl : 0 < l) (hlu : l ≤ u) (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    weightedGeometricPeriodSum B j a b T t S r g h w₁ w₂ w-
      weightedGeometricSmallArcSum B j Q a b T t S r g h w₁ w₂ w =
      (B : ℂ)*∑ k ∈ S,
        (r k : ℂ)*((∫ θ in minorArcRegion B j (Real.exp ((k : ℝ)*t)/T),
          geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ)+
        (∫ θ in largeMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
          geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ)) := by
  unfold weightedGeometricPeriodSum weightedGeometricSmallArcSum
  rw [← mul_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  have hc : Continuous (geometricBoxIntegrand B j a b T t g h w₁ w₂ w k) :=
    ((endpointFourierSum_continuous _ _ _ _ _ _).mul
      ((endpointFourierSum_continuous _ _ _ _ _ _).comp continuous_neg)).mul
      ((smoothCoefficientAdditiveSum_continuous B hl.le hlu (div_pos (Real.exp_pos _) hT) hsupp).comp
        (continuous_const.mul continuous_id))
  rw [majorMinor_integral B j _ hc,majorArc_truncated_integral B j Q _ hc]
  ring

theorem weighted_geometric_period_model_vanishing_jd_oai
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) {M M₀ D₀ R : ℝ}
    (hR : 0 ≤ R)
    (hM0 : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hD₀ : 0 ≤ D₀)
    (hw₁ : ∀ x, |w₁ x| ≤ M) (hw₂ : ∀ x, |w₂ x| ≤ M)
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : Continuous w')
    (hwb : ∀ x, |w x| ≤ M₀) (hwd : ∀ x, |w' x| ≤ D₀)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℝ, 0 < T → η*T ≤ B → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      T*‖weightedGeometricPeriodSum B j a b T t S r g h w₁ w₂ w-
        geometricFullArcSum B j Q a b T t S (fun k => r k*d k) g h w₁ w₂ w‖ ≤ ε B := by
  obtain ⟨c,hc,hcpos,H,ε₁,hε₁,hcoef⟩ := weighted_geometric_coefficient_law_vanishing hSD hSW hM hMP
    ha hab hl hlu ht hη w₁ w₂ w w' hR hM0 hM₀ hD₀ hw₁ hw₂ hw hw' hwb hwd hsupp
  obtain ⟨ε₂,hε₂,hdiscard⟩ := weighted_geometric_discarded_arcs_vanishing hSD hSW hM hMP
    ha hab hl hlu ht w₁ w₂ w w' hR hM0 hM₀ hD₀ hw₁ hw₂ hw hw' hwb hwd hsupp
  refine ⟨c,hc,hcpos,H,fun B => ε₂ B+ε₁ B,by simpa using hε₂.add hε₁,?_⟩
  filter_upwards [hcoef,hdiscard] with B hcoefB hdiscardB
  intro T hT hscale S hbox hlog r hr j _ Q hQ g h hg hh
  dsimp only
  have hfirst := hdiscardB T hT S hbox hlog r hr Q hQ j g h hg hh
  rw [← weighted_geometric_period_split B j Q hT S r g h w₁ w₂ w hl hlu hsupp] at hfirst
  have hsecond := hcoefB T hT hscale S hbox hlog r hr j Q g h hg hh
  exact ((mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) hT.le).trans_eq
    (mul_add _ _ _)).trans (add_le_add hfirst hsecond)

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.weighted_geometric_period_model_vanishing_jd_oai := @OAI.JointDickman.weighted_geometric_period_model_vanishing_jd_oai
