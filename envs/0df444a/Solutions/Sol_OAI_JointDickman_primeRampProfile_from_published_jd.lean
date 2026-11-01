-- Prove2me | solution 1 for OAI.JointDickman.primeRampProfile_from_published_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:14:53.596742+00:00
-- url     : https://prove2.me/submissions/cea28484-cc0f-403a-8414-cc9f2ab68e05

import Mathlib
import Definitions.Def_OAIQ083J003

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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

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

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

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

theorem bernoulliSubsetMass_sum {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S = 1 := by
  simp only [bernoulliSubsetMass]
  rw [← Finset.prod_add]
  simp

/-- The exact finite product formula for a multiplicative tilt. -/
theorem bernoulliSubsetMass_tilt {α : Type*} [DecidableEq α]
    (P : Finset α) (q v : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * (∏ p ∈ S, v p) =
      ∏ p ∈ P, (1 - q p + q p * v p) := by
  calc
    _ = ∑ S ∈ P.powerset,
        (∏ p ∈ S, q p * v p) * ∏ p ∈ P \ S, (1 - q p) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_mul_distrib]
      unfold bernoulliSubsetMass
      ring
    _ = _ := by rw [← Finset.prod_add]; congr 1; ext p; ring

/-- Products of distinct prime sets remember their set of factors. -/
theorem primeProduct_injective {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P)
    (heq : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  have hSF := Nat.primeFactors_prod (fun p hp => hP p (hS hp))
  have hTF := Nat.primeFactors_prod (fun p hp => hP p (hT hp))
  rw [← hSF, ← hTF, heq]

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

theorem uncorrectedSubsetMass_le {P S : Finset ℕ} {q : ℕ → ℝ} (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    uncorrectedSubsetMass P q S ≤ bernoulliSubsetMass P q S := by
  rw [uncorrectedSubsetMass_identity q hS]
  have hp : (∏ p ∈ S, (1 - q p)) ≤ 1 := Finset.prod_le_one
    (fun p hp => sub_nonneg.mpr (hq p (hS hp)).2)
    (fun p hp => by linarith [(hq p (hS hp)).1])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (bernoulliSubsetMass_nonneg hS hq)

theorem uncorrectedSubsetMass_sum (P : Finset ℕ) (q : ℕ → ℝ) :
    (∑ S ∈ P.powerset, uncorrectedSubsetMass P q S) = ∏ p ∈ P, (1 - (q p) ^ 2) := by
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * ∏ p ∈ S, (1 - q p) := by
      apply sum_congr rfl
      intro S hS
      exact uncorrectedSubsetMass_identity q (mem_powerset.mp hS)
    _ = ∏ p ∈ P, (1 - q p + q p * (1 - q p)) := bernoulliSubsetMass_tilt P q _
    _ = _ := prod_congr rfl (fun p _ => by ring)

theorem one_sub_prod_le_sum (P : Finset ℕ) {f : ℕ → ℝ}
    (hf : ∀ p ∈ P, 0 ≤ f p ∧ f p ≤ 1) :
    1 - ∏ p ∈ P, (1 - f p) ≤ ∑ p ∈ P, f p := by
  rw [prod_one_sub_ordered, sub_sub_cancel]
  apply sum_le_sum
  intro p hp
  have hprod : (∏ q ∈ P with q < p, (1 - f q)) ≤ 1 := Finset.prod_le_one
    (fun q hq => sub_nonneg.mpr (hf q (mem_filter.mp hq).1).2)
    (fun q hq => by linarith [(hf q (mem_filter.mp hq).1).1])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (hf p hp).1

open Classical in
theorem uncorrectedSubsetMass_event_error (P : Finset ℕ) (q : ℕ → ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) (E : Finset ℕ → Prop) :
    |(∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P q S else 0) -
      (∑ S ∈ P.powerset, if E S then uncorrectedSubsetMass P q S else 0)| ≤
      ∑ p ∈ P, (q p) ^ 2 := by
  have hδ (S : Finset ℕ) (hS : S ∈ P.powerset) :
      0 ≤ bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S :=
    sub_nonneg.mpr (uncorrectedSubsetMass_le (mem_powerset.mp hS) hq)
  calc
    _ = |∑ S ∈ P.powerset, if E S then
        bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S else 0| := by
      congr 1
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro S _
      split_ifs <;> ring
    _ = ∑ S ∈ P.powerset, if E S then
        bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S else 0 :=
      abs_of_nonneg (sum_nonneg (fun S hS => by split_ifs <;> first | exact hδ S hS | rfl))
    _ ≤ ∑ S ∈ P.powerset, (bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S) := by
      apply sum_le_sum
      intro S hS
      split_ifs <;> first | exact le_refl _ | exact hδ S hS
    _ = 1 - ∏ p ∈ P, (1 - (q p) ^ 2) := by
      rw [sum_sub_distrib, bernoulliSubsetMass_sum, uncorrectedSubsetMass_sum]
    _ ≤ _ := one_sub_prod_le_sum P (fun p hp => ⟨sq_nonneg _, by nlinarith [(hq p hp).1, (hq p hp).2]⟩)

open Classical in
/-- The local mass correction is uniformly small without any restriction
on the event or on the size of the selected prime product. -/
theorem primeSubsetMass_event_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (E : Finset ℕ → Prop) :
    |(∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P (fun p => z / p) S else 0) -
      (∑ S ∈ P.powerset, if E S then uncorrectedSubsetMass P (fun p => z / p) S else 0)| ≤
      z ^ 2 / (N : ℝ) := by
  have hq : ∀ p ∈ P, 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact ⟨div_nonneg hz hp0.le, (div_le_one hp0).mpr (hz1.trans hp1)⟩
  calc
    _ ≤ ∑ p ∈ P, (z / (p : ℝ)) ^ 2 := uncorrectedSubsetMass_event_error P _ hq E
    _ = z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ z ^ 2 * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut) (sq_nonneg z)
    _ = _ := by ring

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

open Classical in
theorem primeProductMass_sum_event (P : Finset ℕ) (z : ℝ) (K : Finset ℕ) :
    (∑ n ∈ K, primeProductMass P z n) =
      ∑ S ∈ P.powerset, if (∏ p ∈ S, p) ∈ K then bernoulliSubsetMass P (fun p => z / p) S else 0 := by
  unfold primeProductMass
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  simp only [eq_comm (a := ∏ p ∈ S, p)]
  simp

open Classical in
theorem uncorrectedPrimeProductMass_sum_event (P : Finset ℕ) (z : ℝ) (K : Finset ℕ) :
    (∑ n ∈ K, uncorrectedPrimeProductMass P z n) =
      ∑ S ∈ P.powerset, if (∏ p ∈ S, p) ∈ K then uncorrectedSubsetMass P (fun p => z / p) S else 0 := by
  unfold uncorrectedPrimeProductMass
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  simp only [eq_comm (a := ∏ p ∈ S, p)]
  simp

/-- The probability of any bounded set differs from its harmonic rough
weight by at most the reciprocal-square prime tail. -/
theorem primeProductMass_harmonic_error {U : ℝ} {N : ℕ} (hN : N ≠ 0)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, (n : ℝ) ≤ U) :
    |(∑ n ∈ K, primeProductMass (largePrimeSet U N) z n) -
      primeNormalizer (largePrimeSet U N) z *
        ∑ n ∈ K, roughSquarefreeWeight (Nat.primesLE N) z n / n| ≤ z ^ 2 / (N : ℝ) := by
  have heq : primeNormalizer (largePrimeSet U N) z *
      (∑ n ∈ K, roughSquarefreeWeight (Nat.primesLE N) z n / n) =
      ∑ n ∈ K, uncorrectedPrimeProductMass (largePrimeSet U N) z n := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [uncorrectedPrimeProductMass_harmonic (hK n hn) z]
    ring
  classical
  have hP : ∀ p ∈ largePrimeSet U (N : ℝ), p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hcut : ∀ p ∈ largePrimeSet U (N : ℝ), N < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have h := primeSubsetMass_event_error (largePrimeSet U (N : ℝ)) hP hN hcut hz hz1
    (fun S : Finset ℕ => (∏ p ∈ S, p) ∈ K)
  rw [heq, primeProductMass_sum_event, uncorrectedPrimeProductMass_sum_event]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  congr 1 <;> apply sum_congr rfl <;> intro S _ <;> split_ifs <;> rfl

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

theorem hasDerivAt_logarithmic_model (c : ℕ → ℝ) (E : Finset ℕ) (z : ℝ) (H : ℕ)
    {Y : ℝ} (hY : 1 < Y) :
    HasDerivAt (fun X => X * ∑ j ∈ range (H + 1),
      roughCoefficient c E z j * (Real.log X) ^ (z - 1 - j))
      (roughDensityPolynomial c E z H (Real.log Y)) Y := by
  have hY0 : 0 < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hterm : ∀ j ∈ range (H + 1),
      HasDerivAt (fun X => X * (roughCoefficient c E z j * (Real.log X) ^ (z - 1 - j)))
        (roughCoefficient c E z j * ((Real.log Y) ^ (z - 1 - j) +
          (z - 1 - j) * (Real.log Y) ^ (z - 2 - j))) Y := by
    intro j _
    have hp := (Real.hasDerivAt_rpow_const (p := z - 1 - j) (Or.inl hlog.ne')).comp Y
      (Real.hasDerivAt_log hY0.ne')
    refine ((hasDerivAt_id Y).mul (hp.const_mul (roughCoefficient c E z j))).congr_deriv (Eq.symm ?_)
    · dsimp only [Function.comp_def, id_eq]
      rw [show z - 1 - (j : ℝ) - 1 = z - 2 - j by ring]
      field_simp
  refine ((HasDerivAt.fun_sum hterm).congr_of_eventuallyEq (Filter.Eventually.of_forall fun X => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    rw [mul_sum]
  · rfl

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_HarmonicSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Partial summation for the local prime-product law

Harmonic weighting of a counting estimate costs only the logarithmic
length of the interval. The finite counting function is kept explicit.
-/

namespace JointDickman

open Finset MeasureTheory
open scoped Interval

theorem sum_div_eq_boundary_add_integral (w : ℕ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, w n / (n : ℝ)) =
      finiteCountingFunction w b / b - finiteCountingFunction w a / a +
        ∫ t in a..b, finiteCountingFunction w t / t ^ 2 := by
  have hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (ha.trans_le ht.1))
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    simp only [deriv_inv']
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg.continuousWithinAt
  have h := sum_mul_eq_sub_sub_integral_mul (c := w) ha.le hab hd hi
  rw [← intervalIntegral.integral_of_le hab] at h
  simp only [deriv_inv] at h
  have heq : (fun t : ℝ => -(t ^ 2)⁻¹ * ∑ n ∈ Icc 0 ⌊t⌋₊, w n) =
      (fun t => -(finiteCountingFunction w t / t ^ 2)) := by
    funext t
    unfold finiteCountingFunction
    ring
  rw [heq, intervalIntegral.integral_neg] at h
  simpa only [div_eq_mul_inv, mul_comm, finiteCountingFunction, sub_neg_eq_add] using h

theorem finiteCountingFunction_div_sq_integrable (w : ℕ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => finiteCountingFunction w t / t ^ 2) volume a b := by
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).continuousWithinAt
  have hi := integrableOn_mul_sum_Icc (m := 0) w ha.le hcont.integrableOn_Icc
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  simpa only [finiteCountingFunction, div_eq_mul_inv, mul_comm] using hi

/-- The integrated counting error is controlled by the logarithmic length. -/
theorem integral_counting_error_le (w : ℕ → ℝ) (F : ℝ → ℝ) {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (herr : ∀ t ∈ Set.Icc a b, |finiteCountingFunction w t - F t| ≤ ε * t) :
    |∫ t in a..b, (finiteCountingFunction w t - F t) / t ^ 2| ≤ ε * Real.log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have hmajor : IntervalIntegrable (fun t => ε / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le (Set.uIcc_of_le hab ▸ ht).1)
    fun_prop
  have h := intervalIntegral.norm_integral_le_of_norm_le hab
    (f := fun t => (finiteCountingFunction w t - F t) / t ^ 2)
    (g := fun t => ε / t) (Filter.Eventually.of_forall (fun t ht => ?_)) hmajor
  · simpa only [Real.norm_eq_abs, div_eq_mul_inv, intervalIntegral.integral_const_mul,
      integral_inv_of_pos ha hb] using h
  have ht0 : 0 < t := ha.trans_le ht.1.le
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos ht0)]
  calc
    _ ≤ ε * t / t ^ 2 := div_le_div_of_nonneg_right (herr t ⟨ht.1.le, ht.2⟩) (sq_nonneg t)
    _ = ε / t := by field_simp

/-- Harmonic weighting loses at most two endpoint errors and one logarithm. -/
theorem harmonic_counting_error_le (w : ℕ → ℝ) (F : ℝ → ℝ) {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hF : ContinuousOn F (Set.Icc a b))
    (herr : ∀ t ∈ Set.Icc a b, |finiteCountingFunction w t - F t| ≤ ε * t) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, w n / (n : ℝ)) -
      (F b / b - F a / a + ∫ t in a..b, F t / t ^ 2)| ≤
        ε * (2 + Real.log (b / a)) := by
  have hb : 0 < b := ha.trans_le hab
  have hFi : IntervalIntegrable (fun t => F t / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hF.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))
  have hGi := finiteCountingFunction_div_sq_integrable w ha hab
  have hint : (∫ t in a..b, finiteCountingFunction w t / t ^ 2) -
      (∫ t in a..b, F t / t ^ 2) =
      ∫ t in a..b, (finiteCountingFunction w t - F t) / t ^ 2 := by
    rw [← intervalIntegral.integral_sub hGi hFi]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hbound (t : ℝ) (ht : t ∈ Set.Icc a b) :
      |(finiteCountingFunction w t - F t) / t| ≤ ε := by
    have ht0 : 0 < t := ha.trans_le ht.1
    rw [abs_div, abs_of_pos ht0]
    exact (div_le_iff₀ ht0).mpr (herr t ht)
  rw [sum_div_eq_boundary_add_integral w ha hab]
  have heq : finiteCountingFunction w b / b - finiteCountingFunction w a / a +
      (∫ t in a..b, finiteCountingFunction w t / t ^ 2) -
      (F b / b - F a / a + ∫ t in a..b, F t / t ^ 2) =
      ((finiteCountingFunction w b - F b) / b - (finiteCountingFunction w a - F a) / a) +
        ((∫ t in a..b, finiteCountingFunction w t / t ^ 2) -
          (∫ t in a..b, F t / t ^ 2)) := by ring
  rw [heq, hint]
  calc
    _ ≤ |(finiteCountingFunction w b - F b) / b| + |(finiteCountingFunction w a - F a) / a| +
        |∫ t in a..b, (finiteCountingFunction w t - F t) / t ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ ε + ε + ε * Real.log (b / a) :=
      add_le_add (add_le_add (hbound b ⟨hab, le_rfl⟩) (hbound a ⟨le_rfl, hab⟩))
        (integral_counting_error_le w F ha hab herr)
    _ = _ := by ring

/-- Integration of the model's derivative gives the same harmonic model. -/
theorem harmonic_model_integral (F M : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hF : ∀ t ∈ Set.Icc a b, HasDerivAt F (M t) t)
    (hM : ContinuousOn M (Set.Icc a b)) :
    (∫ t in a..b, M t / t) = F b / b - F a / a + ∫ t in a..b, F t / t ^ 2 := by
  have hFc : ContinuousOn F (Set.Icc a b) := fun t ht => (hF t ht).continuousAt.continuousWithinAt
  have hMi : IntervalIntegrable (fun t => M t / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hM.div continuousOn_id (fun t ht => ne_of_gt (ha.trans_le ht.1))
  have hFi : IntervalIntegrable (fun t => F t / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hFc.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x => F x / x) (M t / t - F t / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    refine ((hF t ht).div (hasDerivAt_id t) ht0).congr_deriv (Eq.symm ?_)
    · dsimp only [id_eq]
      field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hMi.sub hFi)
  rw [intervalIntegral.integral_sub hMi hFi] at h
  linarith

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughHarmonicLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The harmonic rough coefficient law

Partial summation of the proved moving-cutoff expansion gives the
weighted interval law needed for the independent prime-product model.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughDensityPolynomial_continuousAt (c : ℕ → ℝ) (E : Finset ℕ)
    (z : ℝ) (H : ℕ) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (roughDensityPolynomial c E z H) L := by
  apply tendsto_finsetSum
  intro j _
  apply continuousAt_const.mul
  apply ContinuousAt.add
  · exact continuousAt_id.rpow_const (Or.inl hL.ne')
  · exact continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hL.ne'))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductLogLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-product intervals in logarithmic coordinates

The logarithmic density is the exact change of variables in the harmonic
interval formula, not an independent smoothness assumption.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem scaledRoughDensity_integral (c : ℕ → ℝ) (z : ℝ) (H B : ℕ)
    (hB : 0 < B) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, scaledRoughDensity c z H B s) =
      primeNormalizer (auxiliaryPrimes B) z *
        ∫ t in Real.exp (B * a)..Real.exp (B * b),
          roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let D := roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
  let f := fun s : ℝ => Real.exp (B * s)
  let f' := fun s : ℝ => (B : ℝ) * Real.exp (B * s)
  let g := fun t : ℝ => D (Real.log t) / t
  have hd : ∀ s ∈ Set.uIcc a b, HasDerivAt f (f' s) s := by
    intro s _
    convert ((hasDerivAt_id s).const_mul (B : ℝ)).exp using 1 <;> first | (with_reducible_and_instances rfl) | (simp [f, f', mul_comm])
  have hc : ContinuousOn f' (Set.uIcc a b) := by dsimp [f']; fun_prop
  have hg : ContinuousOn g (f '' Set.uIcc a b) := by
    rintro t ⟨s, hs, rfl⟩
    rw [Set.uIcc_of_le hab] at hs
    have hs0 : 0 < s := ha.trans_le hs.1
    have hpos : 0 < f s := Real.exp_pos _
    have hlog : 0 < Real.log (f s) := by dsimp [f]; rw [Real.log_exp]; positivity
    exact (((roughDensityPolynomial_continuousAt c _ z H hlog).comp
      (Real.continuousAt_log hpos.ne')).div continuousAt_id hpos.ne').continuousWithinAt
  have hchange := intervalIntegral.integral_comp_mul_deriv' hd hc hg
  calc
    _ = ∫ s in a..b, primeNormalizer (auxiliaryPrimes B) z * ((g ∘ f) s * f' s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hab] at hs
      have hs0 : 0 < s := ha.trans_le hs.1
      rw [scaledRoughDensity_eq c z H B hB hs0]
      dsimp [g, f, f', D]
      rw [Real.log_exp]
      field_simp
    _ = primeNormalizer (auxiliaryPrimes B) z * ∫ s in a..b, (g ∘ f) s * f' s :=
      intervalIntegral.integral_const_mul _ _
    _ = _ := by rw [hchange]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductLocalLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform local prime-product law without residue restrictions

This is the modulus-one case of the manuscript's local product law, with
its stated `B^(-80)` absolute error on the shrinking lower-endpoint range.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliary_log_endpoint_conditions {B : ℕ} {a : ℝ}
    (hB : 1 ≤ B) (ha : (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a)
    (hlarge : 9 ≤ (B : ℝ) ^ (9 / 10 : ℝ)) :
    0 < a ∧ 9 ≤ Real.exp (B * a) ∧ (B : ℝ) ^ (89 / 100 : ℝ) ≤ B * a := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  have hpow : (B : ℝ) * (B : ℝ) ^ (-(1 / 10 : ℝ)) = (B : ℝ) ^ (9 / 10 : ℝ) := by
    rw [show (9 / 10 : ℝ) = 1 + -(1 / 10 : ℝ) by norm_num, Real.rpow_add hB0, Real.rpow_one]
  have hBa : (B : ℝ) ^ (9 / 10 : ℝ) ≤ B * a := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left ha hB0.le
  refine ⟨(Real.rpow_pos_of_pos hB0 _).trans_le ha, ?_, ?_⟩
  · have h := Real.add_one_le_exp ((B : ℝ) * a)
    linarith
  · exact (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (89 / 100 : ℝ) ≤ 9 / 10)).trans hBa

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact character-twisted roughness convolution -/

namespace JointDickman

open Finset ArithmeticFunction

theorem characterTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℝ) :
    characterTwist χ (f * g) = characterTwist χ f * characterTwist χ g := by
  ext n
  simp only [characterTwist_apply, mul_apply, Complex.ofReal_sum]
  rw [sum_mul]
  apply sum_congr rfl
  intro ab hab
  have hmul : ab.1 * ab.2 = n := (Nat.mem_divisorsAntidiagonal.mp hab).1
  rw [← hmul, Nat.cast_mul, map_mul, Complex.ofReal_mul]
  ring

theorem roughCharacterSum_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    (E : Finset ℕ) (z Y : ℝ) (V : ℕ) (hV : V ≤ ⌊Y⌋₊) :
    roughCharacterSum χ E z Y =
      (∑ v ∈ Ioc 0 V, (smoothCorrection E z v : ℂ) * χ (v : ZMod q) *
        squarefreeCharacterSum χ z (Y / v)) +
      characterConvolutionTail χ E z ⌊Y⌋₊ V := by
  have hconv := congrArg (characterTwist χ) (squarefreeWeight_mul_smoothCorrection E z)
  rw [characterTwist_mul, mul_comm] at hconv
  change (∑ n ∈ Ioc 0 ⌊Y⌋₊, characterTwist χ (roughSquarefreeWeight E z) n) = _
  rw [← hconv, sum_Ioc_mul_eq_sum_sum,
    ← Ioc_union_Ioc_eq_Ioc (Nat.zero_le V) hV, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1
  · apply sum_congr rfl
    intro v _
    simp only [characterTwist_apply, squarefreeCharacterSum, Nat.floor_div_natCast]
  · simp only [characterConvolutionTail, squarefreeCharacterSum, Nat.floor_natCast,
      characterTwist_apply]

theorem squarefreeCharacterSum_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (N : ℕ) :
    ‖squarefreeCharacterSum χ z N‖ ≤ N := by
  unfold squarefreeCharacterSum
  rw [Nat.floor_natCast]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖(squarefreeWeight z n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul (squarefreeWeight_abs_le_one hz hz1 n)
          (χ.norm_le_one _) (norm_nonneg _) zero_le_one
        _ = _ := by ring
    _ = _ := by simp

/-- Twisting cannot enlarge the Rankin remainder. -/
theorem characterConvolutionTail_rankin {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) {z ε : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 ≤ ε) (N V : ℕ) (hV : 0 < V) :
    ‖characterConvolutionTail χ E z N V‖ ≤
      ((N : ℝ) / (V : ℝ) ^ ε) *
        ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) ^ (1 - ε) := by
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have htail := harmonic_tail_rankin (Ioc V N) (fun v : ℕ => (v : ℝ))
    (fun v => |smoothCorrection E z v|) hV' hε
    (fun v hv => by exact_mod_cast (mem_Ioc.mp hv).1.le)
    (fun _ _ => abs_nonneg _)
  calc
    _ ≤ (N : ℝ) * ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) := by
      unfold characterConvolutionTail
      rw [mul_sum]
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro v hv
      have hvpos : (0 : ℝ) < v := by exact_mod_cast
        ((mem_Ioc.mp hv).1.trans_le' (Nat.zero_le V))
      have hfloor : ((N / v : ℕ) : ℝ) ≤ (N : ℝ) / v := by
        apply (le_div_iff₀ hvpos).mpr
        exact_mod_cast Nat.div_mul_le_self N v
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |smoothCorrection E z v| * ((N / v : ℕ) : ℝ) :=
          mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _))
            (squarefreeCharacterSum_norm_le χ hz hz1 _) (norm_nonneg _) (abs_nonneg _)
        _ ≤ |smoothCorrection E z v| * ((N : ℝ) / v) :=
          mul_le_mul_of_nonneg_left hfloor (abs_nonneg _)
        _ = _ := by ring
    _ ≤ (N : ℝ) * ((∑ v ∈ Ioc V N, |smoothCorrection E z v| /
        (v : ℝ) ^ (1 - ε)) / (V : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inserting the published character bound below the square-root cutoff -/

namespace JointDickman

open Finset

theorem smallCharacterConvolution_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (z Y D : ℝ) (V : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (hY : 1 < Y) (hD : 0 ≤ D)
    (hbound : ∀ v ∈ Ioc 0 V,
      ‖squarefreeCharacterSum χ z (Y / v)‖ ≤
        K * (Y / v) * (Real.log (Y / v)) ^ (-D))
    (hlog : ∀ v ∈ Ioc 0 V, Real.log Y / 2 ≤ Real.log (Y / v)) :
    ‖∑ v ∈ Ioc 0 V, (smoothCorrection E z v : ℂ) * χ (v : ZMod q) *
      squarefreeCharacterSum χ z (Y / v)‖ ≤
        K * Y * (Real.log Y / 2) ^ (-D) *
          ∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ) := by
  have hlogpos : 0 < Real.log Y / 2 := div_pos (Real.log_pos hY) (by norm_num)
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro v hv
  have hpow := Real.rpow_le_rpow_of_nonpos hlogpos (hlog v hv) (neg_nonpos.mpr hD)
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |smoothCorrection E z v| * (K * (Y / v) * (Real.log (Y / v)) ^ (-D)) :=
      mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _))
        (hbound v hv) (norm_nonneg _) (abs_nonneg _)
    _ ≤ |smoothCorrection E z v| * (K * (Y / v) * (Real.log Y / 2) ^ (-D)) := by
      gcongr
    _ = _ := by ring

/-- Uniformity in the modulus is inherited from the published input.
The large-divisor remainder is the actual, already bounded convolution tail. -/
theorem roughCharacterSum_truncated
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (E : Finset ℕ) (Y : ℝ) (V : ℕ),
      9 ≤ Y → (V : ℝ) ^ 2 ≤ Y → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ (Real.log Y / 2) ^ C → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ E z Y‖ ≤
        K * Y * (Real.log Y / 2) ^ (-D) *
          (∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ)) +
        ‖characterConvolutionTail χ E z ⌊Y⌋₊ V‖ := by
  obtain ⟨K, hK, hbound⟩ := hSW z hz C D hC hD
  refine ⟨K, hK, fun E Y V hY hV q _ hq χ hχ => ?_⟩
  obtain ⟨hVN, hsize⟩ := square_root_truncation_conditions hY hV
  have hY1 : 1 < Y := by linarith
  have hsmall := smallCharacterConvolution_bound χ E z Y D V hK hY1 hD
    (fun v hv => hbound (Y / v) (hsize v hv).1 q
      (hq.trans (Real.rpow_le_rpow (by positivity [Real.log_pos hY1])
        (hsize v hv).2 hC.le)) χ hχ)
    (fun v hv => (hsize v hv).2)
  rw [roughCharacterSum_split χ E z Y V hVN]
  exact (norm_add_le _ _).trans (add_le_add hsmall (le_refl _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MovingCharacterBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonprincipal character estimate after removing the small primes -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem roughTruncation_rankin_full {Y : ℝ} {P : ℕ}
    (hY : 0 < Y) (hL : 16 ≤ Real.log Y) (hP : 0 < Real.log P) :
    1 / (roughTruncation Y : ℝ) ^ (1 / Real.log P) ≤
      Real.exp (-(Real.log Y / (8 * Real.log P))) := by
  obtain ⟨hV, _, hlogV⟩ := roughTruncation_bounds hY hL
  have hV0 : (0 : ℝ) < roughTruncation Y := by exact_mod_cast hV
  rw [Real.rpow_def_of_pos hV0, one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hlogV
    (show 0 ≤ 1 / Real.log P by positivity)
  have hpos : 0 ≤ Real.log Y / (8 * Real.log P) := by positivity
  have heq : (Real.log Y / 4) * (1 / Real.log P) =
      2 * (Real.log Y / (8 * Real.log P)) := by ring
  rw [heq] at h
  linarith

/-- Every fixed logarithmic saving survives the convolution, at the
cost of a fixed power of the cutoff logarithm and an explicit Rankin error. -/
theorem roughCharacterSum_exponential
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) (Y : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 9 ≤ Y → 16 ≤ Real.log Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log Y / 2) ^ (200 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ (Nat.primesLE P) z Y‖ ≤
        Y * K * ((Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1 + 1) +
          (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P)))) := by
  obtain ⟨C, hC, hbound⟩ := roughCharacterSum_truncated hSW hz (by norm_num : (0 : ℝ) < 200) hD
  obtain ⟨A, hA, hmom⟩ := smoothCorrection_log_moments_bound hM
  obtain ⟨A', hA', hshift⟩ := smoothCorrection_shifted_bound hM
  let K := C * A * (2 : ℝ) ^ D + A'
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hzh : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  have hK : 0 ≤ K := by dsimp [K] <;> positivity
  refine ⟨K, hK, fun P Y hP hlogP hY hL q _ hq χ hχ => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hLP : 0 < Real.log P := by linarith
  have hLY : 0 < Real.log Y := by linarith
  obtain ⟨hV, hV2, _⟩ := roughTruncation_bounds hY0 hL
  have hmain := hbound (Nat.primesLE P) Y (roughTruncation Y) hY hV2 q hq χ hχ
  have habs : (∑ v ∈ Ioc 0 (roughTruncation Y),
      |smoothCorrection (Nat.primesLE P) z v| / (v : ℝ)) ≤ A * (Real.log P) ^ (Real.exp 1) := by
    simpa using hmom P (Ioc 0 (roughTruncation Y)) z 0 hP hlogP hz0 hzh
  have htail : ‖characterConvolutionTail χ (Nat.primesLE P) z ⌊Y⌋₊ (roughTruncation Y)‖ ≤
      Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
    have ht := characterConvolutionTail_rankin χ (Nat.primesLE P) hz0 (by linarith)
      (by positivity : 0 ≤ 1 / Real.log P) ⌊Y⌋₊ (roughTruncation Y) hV
    calc
      _ ≤ ((⌊Y⌋₊ : ℝ) / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) *
          (A' * (Real.log P) ^ (Real.exp 1)) :=
        ht.trans (mul_le_mul_of_nonneg_left
          (hshift P (Ioc (roughTruncation Y) ⌊Y⌋₊) z hP hlogP hz0 hzh) (by positivity))
      _ ≤ (Y / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) *
          (A' * (Real.log P) ^ (Real.exp 1)) := by
        gcongr
        exact Nat.floor_le hY0.le
      _ = Y * (A' * (Real.log P) ^ (Real.exp 1)) *
          (1 / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) := by ring
      _ ≤ Y * (A' * (Real.log P) ^ (Real.exp 1)) *
          Real.exp (-(Real.log Y / (8 * Real.log P))) :=
        mul_le_mul_of_nonneg_left (roughTruncation_rankin_full hY0 hL hLP) (by positivity)
      _ = _ := by ring
  have hfactor : (Real.log Y / 2) ^ (-D) = (2 : ℝ) ^ D * (Real.log Y) ^ (-D) := by
    rw [Real.div_rpow hLY.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    ring
  have hlogpow : (Real.log P) ^ (Real.exp 1) ≤ (Real.log P) ^ (Real.exp 1 + 1) :=
    Real.rpow_le_rpow_of_exponent_le hlogP (by linarith)
  have hK1 : C * A * (2 : ℝ) ^ D ≤ K := by dsimp [K] <;> linarith
  have hK2 : A' ≤ K := by
    dsimp [K]
    have hpos : 0 ≤ C * A * (2 : ℝ) ^ D := by positivity
    linarith
  calc
    _ ≤ C * Y * (Real.log Y / 2) ^ (-D) * (A * (Real.log P) ^ (Real.exp 1)) +
        Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) :=
      hmain.trans (add_le_add (mul_le_mul_of_nonneg_left habs (by positivity)) htail)
    _ = Y * (C * A * (2 : ℝ) ^ D) * (Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1) +
        Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
      rw [hfactor]
      ring
    _ ≤ Y * K * (Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1 + 1) +
        Y * K * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hK1 hY0.le) (by positivity)) hlogpow (by positivity) (by positivity)
      · gcongr
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterAuxiliaryBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform character cancellation on the manuscript's scale -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem auxiliary_modulus_bound : ∀ᶠ B : ℕ in atTop,
    ∀ L : ℝ, (B : ℝ) ^ (89 / 100 : ℝ) ≤ L →
      (B : ℝ) ^ (100 : ℝ) ≤ (L / 2) ^ (200 : ℝ) := by
  have hlarge : ∀ᶠ B : ℕ in atTop, (2 : ℝ) ≤ (B : ℝ) ^ (39 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 39 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge, eventually_gt_atTop 0] with B hlargeB hB
  intro L hL
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow : (B : ℝ) ^ (1 / 2 : ℝ) ≤ L / 2 := by
    have heq : (B : ℝ) ^ (89 / 100 : ℝ) =
        (B : ℝ) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (39 / 100 : ℝ) := by
      rw [← Real.rpow_add hB0]
      norm_num
    rw [heq] at hL
    nlinarith [Real.rpow_pos_of_pos hB0 (1 / 2 : ℝ)]
  calc
    _ = ((B : ℝ) ^ (1 / 2 : ℝ)) ^ (200 : ℝ) := by
      rw [← Real.rpow_mul hB0.le]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hB0.le _) hpow (by norm_num)

/-- Cancellation after moving small-prime removal holds for all
nonprincipal characters of modulus at most `B^100`. -/
theorem moving_rough_character_bound
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ (Nat.primesLE (auxiliaryCutoff B)) z Y‖ ≤
        K * Y * (B : ℝ) ^ (-D) := by
  let E : ℝ := 2 * (D + 1)
  have hE : 0 ≤ E := by dsimp [E] <;> linarith
  obtain ⟨K, hK, hbound⟩ := roughCharacterSum_exponential hSW hM hz hE
  refine ⟨K, hK, ?_⟩
  have hgap : D + (89 / 100 : ℝ) * ((2 - E) - 2 - (0 : ℕ)) < 0 := by
    dsimp [E]
    norm_num
    linarith
  have hlim := (roughErrorEnvelope_tendsto hgap).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (B : ℝ) ^ D * roughErrorEnvelope (2 - E) 0 B ≤ 1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge : ∀ᶠ B : ℕ in atTop, (16 : ℝ) ≤ (B : ℝ) ^ (89 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 89 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 16)
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlarge, hP, hlog, auxiliary_modulus_bound,
    eventually_gt_atTop 1] with B hs hl hp hlogP hmod hB
  intro Y hY hY9 q _ hq χ hχ
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have henv : roughErrorEnvelope (2 - E) 0 B ≤ (B : ℝ) ^ (-D) := by
    rw [Real.rpow_neg hB0.le, ← one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hB0 D)).mpr (by simpa [mul_comm] using hs)
  have hpoint : (Real.log Y) ^ (-E) *
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + 1) +
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1) *
        Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B)))) ≤
      roughErrorEnvelope (2 - E) 0 B := by
    have h := rough_error_at_auxiliaryCutoff (H := 0) (z := 2 - E) hB
      (by dsimp [E] <;> linarith) hY
    simp only [Nat.cast_zero, sub_zero, Nat.reduceAdd, Nat.cast_one, add_zero] at h
    rw [show 2 - E - 2 = -E by ring] at h
    exact h
  calc
    _ ≤ Y * K * ((Real.log Y) ^ (-E) *
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + 1) +
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1) *
          Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B))))) :=
      hbound (auxiliaryCutoff B) Y hp hlogP hY9 (hl.trans hY) q
        (hq.trans (hmod (Real.log Y) hY)) χ hχ
    _ ≤ Y * K * roughErrorEnvelope (2 - E) 0 B :=
      mul_le_mul_of_nonneg_left hpoint (by positivity)
    _ ≤ Y * K * (B : ℝ) ^ (-D) := mul_le_mul_of_nonneg_left henv (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterResidues
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Character orthogonality for the actual rough coefficients -/

namespace JointDickman

open Finset

open Classical in
theorem progressionSum_characters {q : ℕ} [NeZero q]
    (S : Finset ℕ) (w : ℕ → ℝ) (r : (ZMod q)ˣ) :
    (q.totient : ℂ) * (progressionSum S w (r : ZMod q) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ) *
        ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q) := by
  rw [progressionSum, Complex.ofReal_sum, mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  calc
    _ = (w n : ℂ) * (if (r : ZMod q) = (n : ZMod q) then (q.totient : ℂ) else 0) := by
      split_ifs <;> simp_all
      ring
    _ = (w n : ℂ) * ∑ χ : DirichletCharacter ℂ q,
        χ (r⁻¹ : (ZMod q)ˣ) * χ (n : ZMod q) := by
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ r.isUnit, ZMod.inv_coe_unit]
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro χ _; ring

open Classical in
/-- The normalized character average loses no factor depending on the modulus. -/
theorem progressionSum_error_le {q : ℕ} [NeZero q]
    (S : Finset ℕ) (w : ℕ → ℝ) (r : (ZMod q)ˣ) {E : ℝ} (hE : 0 ≤ E)
    (hunit : ∀ n ∈ S, w n ≠ 0 → IsUnit (n : ZMod q))
    (hbound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ ≤ E) :
    |progressionSum S w (r : ZMod q) - (∑ n ∈ S, w n) / (q.totient : ℝ)| ≤ E := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hprincipal : (∑ n ∈ S, (w n : ℂ) * (1 : DirichletCharacter ℂ q) (n : ZMod q)) =
      (∑ n ∈ S, w n : ℝ) := by
    rw [Complex.ofReal_sum]
    apply sum_congr rfl
    intro n hn
    by_cases hw : w n = 0
    · simp [hw]
    · rw [MulChar.one_apply (hunit n hn hw), mul_one]
  have hid : (q.totient : ℂ) *
      ((progressionSum S w (r : ZMod q) : ℂ) - (∑ n ∈ S, w n : ℝ) / (q.totient : ℂ)) =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q) := by
    have hφ0 : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    rw [mul_sub, mul_div_cancel₀ _ hφ0, progressionSum_characters]
    rw [← sum_erase_add _ _ (mem_univ (1 : DirichletCharacter ℂ q)), hprincipal,
      MulChar.one_apply_coe, one_mul, add_sub_cancel_right]
  have hsum : ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ ≤
      (q.totient : ℝ) * E := by
    calc
      _ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ‖χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, E := by
        apply sum_le_sum
        intro χ hχ
        rw [norm_mul, χ.unit_norm_eq_one, one_mul]
        exact hbound χ (ne_of_mem_erase hχ)
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, E :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => hE)
      _ = _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  rw [← hid, norm_mul, Complex.norm_natCast] at hsum
  have heq : ‖(progressionSum S w (r : ZMod q) : ℂ) - (∑ n ∈ S, w n : ℝ) / (q.totient : ℂ)‖ =
      |progressionSum S w (r : ZMod q) - (∑ n ∈ S, w n) / (q.totient : ℝ)| := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [heq] at hsum
  exact (mul_le_mul_iff_right₀ hφ).mp hsum

theorem roughSquarefreeWeight_coprime {P q n : ℕ} (hq : q ≠ 0) (hqP : q ≤ P)
    (z : ℝ) (hn : roughSquarefreeWeight (Nat.primesLE P) z n ≠ 0) : n.Coprime q := by
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
  have hd : Disjoint n.primeFactors (Nat.primesLE P) := by
    by_contra h
    simp [roughSquarefreeWeight, h] at hn
  by_contra h
  obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact disjoint_left.mp hd (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩)
    (Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hpq).trans hqP, hp⟩)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueSummatory
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform progression estimate for rough squarefree integers -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem auxiliary_modulus_le_cutoff {B q : ℕ} (hB : 1 ≤ B)
    (hq : (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ)) : q ≤ auxiliaryCutoff B := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hcut : (auxiliaryCutoff B : ℝ) = (B : ℝ) ^ (1000 : ℝ) := by
    norm_num [auxiliaryCutoff]
  have hle := hq.trans (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (100 : ℝ) ≤ 1000))
  rw [← hcut] at hle
  exact_mod_cast hle

/-- Equidistribution in the unit classes, before partial summation. -/
theorem roughResidueSummatory_error
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ r : (ZMod q)ˣ,
      |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient| ≤
        K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨K, hK, hbound⟩ := moving_rough_character_bound hSW hM hz hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro Y hY hY9 q _ hq r
  have hqP := auxiliary_modulus_le_cutoff hB hq
  exact progressionSum_error_le (Ioc 0 ⌊Y⌋₊)
    (roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z) r (by positivity)
    (fun n _ hn => (ZMod.isUnit_iff_coprime n q).mpr
      (roughSquarefreeWeight_coprime (NeZero.ne q) hqP z hn))
    (fun χ hχ => hboundB Y hY hY9 q hq χ hχ)

/-- The same actual coefficients as the untwisted expansion serve in
all unit progressions; the error is uniform in every modulus up to `B^100`. -/
theorem roughResidueSummatory_expansion
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
          (Y * ∑ ν ∈ range (H + 1),
            roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν *
              (Real.log Y) ^ (z - 1 - ν)) / q.totient| ≤
          K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := moving_rough_auxiliary_expansion hSD hM hz D
  obtain ⟨K', hK', hres⟩ := roughResidueSummatory_error hSW hM hz hD
  refine ⟨c, hc0, hcpos, H, K + K', add_nonneg hK hK', ?_⟩
  filter_upwards [hbound, hres] with B hboundB hresB
  intro Y hY hY9 q _ hq r
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hφ0 : (0 : ℝ) < q.totient := by linarith
  have hu := hboundB Y hY hY9
  have hr := hresB Y hY hY9 q hq r
  let T := Y * ∑ ν ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν * (Real.log Y) ^ (z - 1 - ν)
  have hdiv : |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient -
      T / q.totient| ≤ K * Y * (B : ℝ) ^ (-D) := by
    rw [← sub_div, abs_div, abs_of_pos hφ0]
    exact (div_le_self (abs_nonneg _) hφ).trans hu
  calc
    _ ≤ |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient| +
        |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient -
          T / q.totient| := abs_sub_le _ _ _
    _ ≤ K' * Y * (B : ℝ) ^ (-D) + K * Y * (B : ℝ) ^ (-D) := add_le_add hr hdiv
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughResidueHarmonic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partial summation in the unit residue classes -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem finiteCountingFunction_roughResidue {q : ℕ} (r : ZMod q)
    (E : Finset ℕ) (z t : ℝ) :
    finiteCountingFunction (roughResidueWeight r E z) t = roughResidueSummatory r E z t := by
  unfold finiteCountingFunction roughResidueSummatory progressionSum roughResidueWeight
  rw [← Ioc_insert_left (Nat.zero_le ⌊t⌋₊), sum_insert left_notMem_Ioc]
  simp

theorem rough_residue_harmonic_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
            roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
          (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
            (Real.log t) / t) / q.totient| ≤
          K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := roughResidueSummatory_expansion hSD hSW hM hz hD
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound] with B hB
  intro a b ha hab hlog q _ hq r
  have ha0 : 0 < a := by linarith
  let E := Nat.primesLE (auxiliaryCutoff B)
  let F := fun t : ℝ => (t * ∑ j ∈ range (H + 1),
    roughCoefficient c E z j * (Real.log t) ^ (z - 1 - j)) / (q.totient : ℝ)
  let M := fun t : ℝ => roughDensityPolynomial c E z H (Real.log t) / (q.totient : ℝ)
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt F (M t) t :=
    (hasDerivAt_logarithmic_model c E z H (by linarith [ht.1])).div_const _
  have hFc : ContinuousOn F (Set.Icc a b) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hMc : ContinuousOn M (Set.Icc a b) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact (((roughDensityPolynomial_continuousAt c E z H (Real.log_pos ht1)).comp
      (Real.continuousAt_log (by linarith : t ≠ 0))).div_const _).continuousWithinAt
  have herr : ∀ t ∈ Set.Icc a b,
      |finiteCountingFunction (roughResidueWeight (r : ZMod q) E z) t - F t| ≤
        (K * (B : ℝ) ^ (-D)) * t := by
    intro t ht
    have hlogt : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log t :=
      hlog.trans (Real.log_le_log ha0 ht.1)
    simpa only [finiteCountingFunction_roughResidue, F, E, mul_assoc, mul_left_comm, mul_comm] using
      hB t hlogt (ha.trans ht.1) q hq r
  have h := harmonic_counting_error_le (roughResidueWeight (r : ZMod q) E z) F ha0 hab hFc herr
  rw [← harmonic_model_integral F M ha0 hab hd hMc] at h
  have hint : (∫ t in a..b, M t / t) =
      (∫ t in a..b, roughDensityPolynomial c E z H (Real.log t) / t) / q.totient := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [M]
    ring
  rw [hint] at h
  exact h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductResidueInterval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-product interval probabilities with a unit residue restriction -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem sum_roughResidueWeight_div {q : ℕ} (S : Finset ℕ) (r : ZMod q)
    (E : Finset ℕ) (z : ℝ) :
    (∑ n ∈ S.filter (fun (n : ℕ) => (n : ZMod q) = r), roughSquarefreeWeight E z n / (n : ℝ)) =
      ∑ n ∈ S, roughResidueWeight r E z n / (n : ℝ) := by
  rw [sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases h : (n : ZMod q) = r <;> simp [roughResidueWeight, h]

open Classical in
theorem primeProduct_residue_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        9 ≤ a → a ≤ b → b ≤ auxiliaryUpper B →
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
            primeProductMass (auxiliaryPrimes B) z n) -
          primeNormalizer (auxiliaryPrimes B) z *
            (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
              (Real.log t) / t) / q.totient| ≤
          z ^ 2 / (auxiliaryCutoff B : ℝ) +
            K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hrough⟩ := rough_residue_harmonic_interval_law hSD hSW hM hz hD
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hrough, eventually_gt_atTop 0] with B hB hB0
  intro a b ha hab hb hlog q _ hq r
  have hb0 : 0 ≤ b := by linarith
  have hcut : auxiliaryCutoff B ≠ 0 := pow_ne_zero 1000 (Nat.ne_of_gt hB0)
  have hmass := primeProductMass_harmonic_error (U := auxiliaryUpper B) hcut hz0 hz1
    ((Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun n => (n : ZMod q) = (r : ZMod q))) (fun n hn =>
      ((by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).2 : (n : ℝ) ≤ ⌊b⌋₊).trans
        (Nat.floor_le hb0)).trans hb)
  rw [sum_roughResidueWeight_div] at hmass
  have hQ := primeNormalizer_bounds (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hz0 hz1
  have hweighted : |primeNormalizer (auxiliaryPrimes B) z *
      ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
          roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
        (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
          (Real.log t) / t) / q.totient)| ≤
      K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
    rw [abs_mul, abs_of_nonneg hQ.1]
    simpa only [one_mul] using mul_le_mul hQ.2 (hB a b ha hab hlog q hq r)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ = |((∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
          primeProductMass (auxiliaryPrimes B) z n) - primeNormalizer (auxiliaryPrimes B) z *
            ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
              roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) +
        primeNormalizer (auxiliaryPrimes B) z *
          ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
              roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
            (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
              (Real.log t) / t) / q.totient)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hmass hweighted)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductResidueLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform residue-restricted local prime-product law -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- The actual prime-product probability of a log-coordinate interval in a unit class. -/
theorem primeProduct_residue_log_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        0 < a → a ≤ b → b ≤ 4 →
        9 ≤ Real.exp (B * a) → (B : ℝ) ^ (89 / 100 : ℝ) ≤ B * a →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ (Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
            primeProductMass (auxiliaryPrimes B) z n) -
          (∫ s in a..b, scaledRoughDensity c z H B s) / q.totient| ≤
          z ^ 2 / (auxiliaryCutoff B : ℝ) + K * (B : ℝ) ^ (-D) * (2 + B * (b - a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := primeProduct_residue_interval_law hSD hSW hM hz hD
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hB hB0
  intro a b ha hab hb hsize hscale q _ hq r
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB0
  have hexp : Real.exp (B * a) ≤ Real.exp (B * b) := Real.exp_le_exp.mpr (by nlinarith)
  have hupper : Real.exp (B * b) ≤ auxiliaryUpper B := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h := hB (Real.exp (B * a)) (Real.exp (B * b)) hsize hexp hupper
    (by simpa only [Real.log_exp] using hscale) q hq r
  rw [← scaledRoughDensity_integral c z H B hB0 ha hab] at h
  have hlog : Real.log (Real.exp (B * b) / Real.exp (B * a)) = B * (b - a) := by
    rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    ring
  simpa only [hlog] using h


open Classical in
/-- All intervals in the range have the same absolute error constant. -/
theorem primeProduct_residue_local_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ (Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
            primeProductMass (auxiliaryPrimes B) z n) -
          (∫ s in a..b, scaledRoughDensity c z H B s) / q.totient| ≤ C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := primeProduct_residue_log_interval_law hSD hSW hM hz (by norm_num : (0 : ℝ) ≤ 81)
  refine ⟨c, hc0, hcpos, H, 1 + 6 * K, by positivity, ?_⟩
  have hlarge : ∀ᶠ B : ℕ in atTop, (9 : ℝ) ≤ (B : ℝ) ^ (9 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 9)
  filter_upwards [hbound, hlarge, eventually_ge_atTop 1] with B hB hlargeB hB1
  intro a b ha hab hb q _ hq r
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hB0 : (0 : ℝ) < B := by linarith
  obtain ⟨ha0, hsize, hscale⟩ := auxiliary_log_endpoint_conditions hB1 ha hlargeB
  have h := hB a b ha0 hab (by linarith) hsize hscale q hq r
  have hzsq : z ^ 2 ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have htail : z ^ 2 / (auxiliaryCutoff B : ℝ) ≤ (B : ℝ) ^ (-(80 : ℝ)) := by
    calc
      _ ≤ 1 / (auxiliaryCutoff B : ℝ) :=
        div_le_div_of_nonneg_right hzsq (by positivity)
      _ = (B : ℝ) ^ (-(1000 : ℝ)) := by
        rw [Real.rpow_neg hB0.le]
        norm_num [auxiliaryCutoff]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hBreal (by norm_num)
  have hlen : 2 + (B : ℝ) * (b - a) ≤ 6 * B := by nlinarith
  have hpoly : K * (B : ℝ) ^ (-(81 : ℝ)) * (2 + (B : ℝ) * (b - a)) ≤
      6 * K * (B : ℝ) ^ (-(80 : ℝ)) := by
    calc
      _ ≤ K * (B : ℝ) ^ (-(81 : ℝ)) * (6 * B) :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = _ := by
        have heq : (B : ℝ) ^ (-(81 : ℝ)) * B = (B : ℝ) ^ (-(80 : ℝ)) := by
          rw [show (-(80 : ℝ)) = -81 + 1 by norm_num, Real.rpow_add hB0, Real.rpow_one]
        nlinarith [heq]
  calc
    _ ≤ z ^ 2 / (auxiliaryCutoff B : ℝ) +
        K * (B : ℝ) ^ (-(81 : ℝ)) * (2 + B * (b - a)) := h
    _ ≤ (B : ℝ) ^ (-(80 : ℝ)) + 6 * K * (B : ℝ) ^ (-(80 : ℝ)) := add_le_add htail hpoly
    _ = _ := by ring


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_IndependentKernelSplit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The independent common/exclusive model and its cutoff

The three independent category bits are reindexed as three independent
Boolean prime subsets. Their products are the common product and the two
exclusive products. The low-exclusive union is separated exactly; the
complement is the product of the two high-exclusive cell probabilities.
-/

namespace JointDickman

open scoped BigOperators

section Cutoff

variable {C E A : Type*} [Fintype C] [Fintype E] [DecidableEq A]

omit [Fintype C] in
theorem highExclusiveCell_eq_sum (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low] (c : C) (a : A) :
    highExclusiveCell v cell low c a =
      ∑ e, if ¬low e ∧ cell c e = some a then v e else 0 := by
  unfold highExclusiveCell optionCellMass
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : low e <;> by_cases hc : cell c e = some a <;> simp [hl, hc]

end Cutoff

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSiteBridge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact equivalence of prime-site and prime-subset probabilities -/

namespace JointDickman

open Finset

theorem selectedPrimeSubset_subset (Q : Finset ℕ) (x : Q → Bool) :
    selectedPrimeSubset Q x ⊆ Q := filter_subset _ _

theorem selectedPrimeSubset_injective (Q : Finset ℕ) : Function.Injective (selectedPrimeSubset Q) := by
  intro x y hxy
  funext p
  have h : x p = true ↔ y p = true := by
    rw [← selectedPrimeSubset_mem Q x p, ← selectedPrimeSubset_mem Q y p, hxy]
  cases hx : x p <;> cases hy : y p <;> simp_all

open Classical in
theorem selectedPrimeSubset_surjective (Q S : Finset ℕ) (hS : S ⊆ Q) :
    ∃ x : Q → Bool, selectedPrimeSubset Q x = S := by
  refine ⟨fun p => decide (p.val ∈ S), ?_⟩
  ext p
  by_cases hp : p ∈ Q
  · simp [selectedPrimeSubset, hp]
  · have hpS : p ∉ S := fun h => hp (hS h)
    simp [selectedPrimeSubset, hp, hpS]

theorem retainedPrimeProduct_selected (Q : Finset ℕ) (x : Q → Bool) :
    retainedPrimeProduct Q x = ∏ p ∈ selectedPrimeSubset Q x, p := by
  have hfilter : Q.filter (fun p => p ∈ selectedPrimeSubset Q x) = selectedPrimeSubset Q x := by
    ext p
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun h => selectedPrimeSubset_subset Q x h
  calc
    _ = ∏ p : Q, if p.val ∈ selectedPrimeSubset Q x then p.val else 1 := by
      apply prod_congr rfl
      intro p _
      simp only [selectedPrimeSubset_mem]
    _ = ∏ p ∈ Q, if p ∈ selectedPrimeSubset Q x then p else 1 :=
      prod_coe_sort Q (fun p : ℕ => if p ∈ selectedPrimeSubset Q x then p else 1)
    _ = _ := by rw [prod_ite, hfilter]; simp

theorem bernoulliSiteMass_selected (Q : Finset ℕ) (q : ℕ → ℝ) (x : Q → Bool) :
    bernoulliSiteMass (fun p : Q => q p.val) x = bernoulliSubsetMass Q q (selectedPrimeSubset Q x) := by
  have hfilter : Q.filter (fun p => p ∈ selectedPrimeSubset Q x) = selectedPrimeSubset Q x := by
    ext p
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun h => selectedPrimeSubset_subset Q x h
  have hfilter' : Q.filter (fun p => p ∉ selectedPrimeSubset Q x) = Q \ selectedPrimeSubset Q x := by
    ext p
    simp
  calc
    _ = ∏ p : Q, if p.val ∈ selectedPrimeSubset Q x then q p.val else 1 - q p.val := by
      apply prod_congr rfl
      intro p _
      simp only [selectedPrimeSubset_mem]
      cases x p <;> rfl
    _ = ∏ p ∈ Q, if p ∈ selectedPrimeSubset Q x then q p else 1 - q p :=
      prod_coe_sort Q (fun p : ℕ => if p ∈ selectedPrimeSubset Q x then q p else 1 - q p)
    _ = _ := by rw [prod_ite, hfilter, hfilter']; rfl

open Classical in
/-- This equality transfers every event, not just an interval or a residue class. -/
theorem bernoulliPrimeSite_event (Q : Finset ℕ) (q : ℕ → ℝ) (A : ℕ → Prop) :
    (∑ x : Q → Bool, if A (retainedPrimeProduct Q x) then
      bernoulliSiteMass (fun p : Q => q p.val) x else 0) =
      ∑ S ∈ Q.powerset, if A (∏ p ∈ S, p) then bernoulliSubsetMass Q q S else 0 := by
  apply sum_bij (fun x _ => selectedPrimeSubset Q x)
  · intro x _
    exact mem_powerset.mpr (selectedPrimeSubset_subset Q x)
  · intro x _ y _ h
    exact selectedPrimeSubset_injective Q h
  · intro S hS
    obtain ⟨x, hx⟩ := selectedPrimeSubset_surjective Q S (mem_powerset.mp hS)
    exact ⟨x, mem_univ _, hx⟩
  · intro x _
    rw [retainedPrimeProduct_selected, bernoulliSiteMass_selected]


open Classical in
theorem primeSiteMass_event (Q : Finset ℕ) (z : ℝ) (K : Finset ℕ) :
    (∑ x : Q → Bool, if retainedPrimeProduct Q x ∈ K then
      bernoulliSiteMass (fun p : Q => z / p.val) x else 0) =
      ∑ n ∈ K, primeProductMass Q z n := by
  rw [primeProductMass_sum_event]
  have h := bernoulliPrimeSite_event Q (fun p : ℕ => z / p) (fun n => n ∈ K)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (apply sum_congr rfl <;> intro n _ <;> split_ifs <;> rfl)

theorem quarterPrimeMass_eq (Q : Finset ℕ) (x : Q → Bool) :
    quarterPrimeMass Q x = bernoulliSiteMass (fun p : Q => (1 / 4 : ℝ) / p.val) x := by
  unfold quarterPrimeMass
  congr 1
  funext p
  ring

theorem retainedPrimeProduct_pos (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (x : Q → Bool) :
    0 < retainedPrimeProduct Q x := by
  rw [retainedPrimeProduct_selected]
  exact prod_pos (fun p hp => (hQ p (selectedPrimeSubset_subset Q x hp)).pos)

theorem retainedPrimeProduct_coprime (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    {q : ℕ} (hq : q ≠ 0) (hcut : ∀ p ∈ Q, q < p) (x : Q → Bool) :
    (retainedPrimeProduct Q x).Coprime q := by
  rw [retainedPrimeProduct_selected, Nat.coprime_prod_left_iff]
  intro p hp
  have hpQ := selectedPrimeSubset_subset Q x hp
  apply (hQ p hpQ).coprime_iff_not_dvd.mpr
  intro hdiv
  exact (not_le_of_gt (hcut p hpQ)) (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdiv)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSiteLocalLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local product laws for the actual Boolean prime sites -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem primeSite_local_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ x : auxiliaryPrimes B → Bool,
          if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
              (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r then
            bernoulliSiteMass (fun p : auxiliaryPrimes B => z / p.val) x else 0) -
          (∫ s in a..b, scaledRoughDensity c z H B s) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨c, hc, hcpos, H, C, hC, hbound⟩ := primeProduct_residue_local_interval_law hSD hSW hM hz
  refine ⟨c, hc, hcpos, H, C, hC, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hboundB hB
  intro a b ha hab hb q _ hq r
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let K := (Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊).filter
    (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q))
  have hevent (x : auxiliaryPrimes B → Bool) :
      (Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
        (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r) ↔
      retainedPrimeProduct (auxiliaryPrimes B) x ∈ K := by
    have hnpos : (0 : ℝ) < retainedPrimeProduct (auxiliaryPrimes B) x := by
      exact_mod_cast retainedPrimeProduct_pos (auxiliaryPrimes B) (auxiliaryPrimes_prime B) x
    simp only [K, mem_filter, mem_Ioc, Set.mem_Ioc]
    rw [Nat.floor_lt (by positivity : 0 ≤ Real.exp (B * a)), Nat.le_floor_iff (by positivity : 0 ≤ Real.exp (B * b))]
    rw [lt_div_iff₀ hB0, div_le_iff₀ hB0]
    rw [Real.lt_log_iff_exp_lt hnpos, Real.log_le_iff_le_exp hnpos]
    ring_nf
  have hsum : (∑ x : auxiliaryPrimes B → Bool,
      if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r then
        bernoulliSiteMass (fun p : auxiliaryPrimes B => z / p.val) x else 0) =
        ∑ n ∈ K, primeProductMass (auxiliaryPrimes B) z n := by
    simp_rw [hevent]
    exact primeSiteMass_event (auxiliaryPrimes B) z K
  rw [hsum]
  exact hboundB a b ha hab hb q hq r


open Classical in
theorem quarterPrimeSite_local_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 4) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ x : auxiliaryPrimes B → Bool,
          if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
              (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r then
            quarterPrimeMass (auxiliaryPrimes B) x else 0) -
          (∫ s in a..b, scaledRoughDensity c (1 / 4) H B s) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  have h := primeSite_local_law hSD hSW hM
    (Or.inl rfl : (1 / 4 : ℝ) = 1 / 4 ∨ (1 / 4 : ℝ) = 1 / 2)
  simpa only [quarterPrimeMass_eq] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProductLogCells
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual logarithmic and residue cells, with partial output -/

namespace JointDickman

open Finset

open Classical in
theorem logResidueCell_eq_some {D : Type*} (B q : ℕ) (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (n : ℕ) (d : D) (r : (ZMod q)ˣ) :
    logResidueCell B q lower upper n = some (d, r) ↔
      Real.log n / B ∈ Set.Ioc (lower d) (upper d) ∧ (n : ZMod q) = r := by
  unfold logResidueCell
  by_cases hn : n.Coprime q
  · rw [dite_eq_left hn]
    by_cases hi : ∃ e, Real.log n / B ∈ Set.Ioc (lower e) (upper e)
    · rw [dite_eq_left hi, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hd, hr⟩
        subst d
        exact ⟨hi.choose_spec, by rw [← hr]; rfl⟩
      · rintro ⟨hd, hr⟩
        exact ⟨hdisjoint hi.choose d _ hi.choose_spec hd, Units.ext hr⟩
    · rw [dite_eq_right hi]
      simp only [reduceCtorEq, false_iff, not_and]
      exact fun hd => False.elim (hi ⟨d, hd⟩)
  · rw [dite_eq_right hn]
    simp only [reduceCtorEq, false_iff, not_and]
    intro _ hr
    have hu : IsUnit (n : ZMod q) := hr ▸ r.isUnit
    exact hn ((ZMod.isUnit_iff_coprime n q).mp hu)

/-- Multiplication by the common product translates the log cell and
permutes the unit residue. The high-exclusive cutoff changes only the
lower endpoint. -/
theorem high_product_cell_iff {B c n q : ℕ} (hc : 0 < c) (hn : 0 < n)
    (u r : (ZMod q)ˣ) (hu : (c : ZMod q) = u) (a b θ : ℝ) :
    (θ < Real.log n / B ∧
      Real.log (c * n : ℕ) / B ∈ Set.Ioc a b ∧ ((c * n : ℕ) : ZMod q) = (r : ZMod q)) ↔
    (Real.log n / B ∈ Set.Ioc (max θ (a - Real.log c / B)) (b - Real.log c / B) ∧
      (n : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)) := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (c * n : ℕ) / B = Real.log c / B + Real.log n / B := by
    rw [Nat.cast_mul, Real.log_mul hc0.ne' hn0.ne', add_div]
  have hmod : ((c * n : ℕ) : ZMod q) = r ↔ (n : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ) := by
    rw [Nat.cast_mul, hu]
    constructor
    · intro h
      have h' := congrArg (fun t : ZMod q => (u⁻¹ : (ZMod q)ˣ) * t) h
      simpa [mul_assoc] using h'
    · intro h
      rw [h]
      simp [← Units.val_mul]
  rw [hlog, hmod]
  simp only [Set.mem_Ioc, max_lt_iff]
  constructor
  · rintro ⟨hθ, hab, hr⟩
    exact ⟨⟨⟨hθ, by linarith [hab.1]⟩, by linarith [hab.2]⟩, hr⟩
  · rintro ⟨⟨⟨hθ, ha⟩, hb⟩, hr⟩
    exact ⟨hθ, ⟨by linarith, by linarith⟩, hr⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HighExclusiveLocalLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local laws for the high-exclusive part of the actual prime channel -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem highExclusiveLogCell_eq {D : Type*} [DecidableEq D]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (B q : ℕ) (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (θ : ℝ) (c : Q → Bool) (u r : (ZMod q)ˣ)
    (hu : (retainedPrimeProduct Q c : ZMod q) = u) (d : D) :
    highExclusiveCell (quarterPrimeMass Q)
      (primeProductCell Q (logResidueCell B q lower upper)) (lowPrimeLog Q B θ) c (d, r) =
      ∑ e : Q → Bool,
        if Real.log (retainedPrimeProduct Q e) / B ∈
            Set.Ioc (max θ (lower d - Real.log (retainedPrimeProduct Q c) / B))
              (upper d - Real.log (retainedPrimeProduct Q c) / B) ∧
          (retainedPrimeProduct Q e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ) then
          quarterPrimeMass Q e else 0 := by
  rw [highExclusiveCell_eq_sum]
  apply sum_congr rfl
  intro e _
  have hiff : (¬lowPrimeLog Q B θ e ∧
      primeProductCell Q (logResidueCell B q lower upper) c e = some (d, r)) ↔
      (Real.log (retainedPrimeProduct Q e) / B ∈
        Set.Ioc (max θ (lower d - Real.log (retainedPrimeProduct Q c) / B))
          (upper d - Real.log (retainedPrimeProduct Q c) / B) ∧
        (retainedPrimeProduct Q e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)) := by
    dsimp only [lowPrimeLog, primeProductCell]
    rw [not_le, logResidueCell_eq_some B q lower upper hdisjoint]
    exact high_product_cell_iff (retainedPrimeProduct_pos Q hQ c)
      (retainedPrimeProduct_pos Q hQ e) u r hu (lower d) (upper d) θ
  simp only [hiff]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HighExclusiveThreshold
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # High-exclusive local law for fixed smoothing thresholds -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- The retained exclusive cell is approximated by a residue-independent
integral, uniformly even for a partial cell at the high cutoff. -/
theorem highExclusiveLogCell_threshold_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ v : ℕ → ℝ, v 0 = squarefreeLeadingConstant (1 / 4) ∧ 0 < v 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ θ : ℝ, (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ θ →
        ∀ lower upper : D → ℝ,
        (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
        (∀ d, upper d ≤ 16 / 5) → ∀ c : auxiliaryPrimes B → Bool, ∀ d : D, ∀ r : (ZMod q)ˣ,
        |highExclusiveCell (quarterPrimeMass (auxiliaryPrimes B))
            (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper))
            (lowPrimeLog (auxiliaryPrimes B) B θ) c (d, r) -
          clippedIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
            θ (lower d) (upper d)
            (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨v, hv, hvpos, H, C, hC, hbound⟩ := quarterPrimeSite_local_law hSD hSW hM
  refine ⟨v, hv, hvpos, H, C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro D _ q _ hq θ hθ lower upper hdisjoint hupper c d r
  have hqP := auxiliary_modulus_le_cutoff hB hq
  have hcut : ∀ p ∈ auxiliaryPrimes B, q < p := by
    intro p hp
    have hP : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp hp).2
    exact hqP.trans_lt hP
  let u := ZMod.unitOfCoprime (retainedPrimeProduct (auxiliaryPrimes B) c)
    (retainedPrimeProduct_coprime (auxiliaryPrimes B) (auxiliaryPrimes_prime B) (NeZero.ne q) hcut c)
  rw [highExclusiveLogCell_eq (auxiliaryPrimes B) (auxiliaryPrimes_prime B) B q lower upper
    hdisjoint _ c u r rfl d]
  let t := Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / (B : ℝ)
  have ht : 0 ≤ t := div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  let a := max θ (lower d - t)
  let b := upper d - t
  by_cases hab : a ≤ b
  · have ha : (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a := hθ.trans (le_max_left _ _)
    have hb : b ≤ 16 / 5 := by dsimp [b] <;> linarith [hupper d]
    have hh := hboundB a b ha hab hb q hq (u⁻¹ * r)
    simpa only [clippedIntervalIntegral, t, a, b, ite_eq_left hab] using hh
  · have hempty : ∀ e : auxiliaryPrimes B → Bool,
        ¬(Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)) := by
      rintro e ⟨he, _⟩
      exact hab (le_trans he.1.le he.2)
    have hsum : (∑ e : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)
        then quarterPrimeMass (auxiliaryPrimes B) e else 0) = 0 := by
      apply sum_eq_zero
      intro e _
      exact ite_eq_right (hempty e)
    change |(∑ e : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)
        then quarterPrimeMass (auxiliaryPrimes B) e else 0) - _| ≤ _
    have hclip : clippedIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
        θ (lower d) (upper d)
        (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) = 0 := by
      change (if a ≤ b then _ else 0) = 0
      exact ite_eq_right hab
    rw [hsum, hclip]
    simp only [zero_div, sub_self, abs_zero]
    positivity


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An averaged sharp cutoff for the coarse channel -/

namespace JointDickman

open MeasureTheory
open scoped NNReal

theorem averagingRamp_bounds {a b : ℝ} (hab : a < b) (x : ℝ) :
    0 ≤ averagingRamp a b x ∧ averagingRamp a b x ≤ 1 := by
  have hlo : a ≤ min b (max a x) := le_min hab.le (le_max_left _ _)
  have hhi : min b (max a x) ≤ b := min_le_left _ _
  unfold averagingRamp
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hab).le
  · apply (div_le_one (sub_pos.mpr hab)).mpr
    linarith

open Classical in
theorem integral_strict_cutoff {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    (∫ t in a..b, if t < x then (1 : ℝ) else 0) = min b (max a x) - a := by
  have hae : (fun t : ℝ => if t < x then (1 : ℝ) else 0) =ᵐ[volume]
      (fun t : ℝ => if t ≤ x then (1 : ℝ) else 0) := by
    filter_upwards [volume.ae_ne x] with t ht
    have he : (t < x) ↔ t ≤ x := ⟨le_of_lt, fun h => lt_of_le_of_ne h ht⟩
    simp only [he]
  rw [intervalIntegral.integral_congr_ae (hae.mono (fun _ h _ => h))]
  by_cases hxa : x < a
  · have hi : (∫ t in a..b, if t ≤ x then (1 : ℝ) else 0) = 0 := by
      calc
        _ = ∫ _t in a..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hab
          intro t ht
          exact ite_eq_right (by linarith [ht.1])
        _ = 0 := intervalIntegral.integral_zero
    rw [hi, max_eq_left hxa.le, min_eq_right hab, sub_self]
  · have hax := le_of_not_gt hxa
    by_cases hbx : b ≤ x
    · have hi : (∫ t in a..b, if t ≤ x then (1 : ℝ) else 0) = b - a := by
        calc
          _ = ∫ _t in a..b, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have ht' : t ≤ b := (Set.uIcc_of_le hab ▸ ht).2
            exact ite_eq_left (ht'.trans hbx)
          _ = _ := by simp
      rw [hi, max_eq_right hax, min_eq_left hbx]
    · have hxb := le_of_not_ge hbx
      have h := intervalIntegral.integral_indicator (μ := volume) (f := fun _ : ℝ => (1 : ℝ))
        (show x ∈ Set.Icc a b from ⟨hax, hxb⟩)
      simpa [Set.indicator, max_eq_right hax, min_eq_right hxb] using h

open Classical in
theorem averagingRamp_integral {a b : ℝ} (hab : a < b) (x : ℝ) :
    averagingRamp a b x = (∫ t in a..b, if t < x then (1 : ℝ) else 0) / (b - a) := by
  rw [integral_strict_cutoff hab.le]
  rfl

theorem averagingRamp_lipschitz {a b : ℝ} (hab : a < b) :
    LipschitzWith ⟨1 / (b - a), by positivity⟩ (averagingRamp a b) := by
  have hclip := (LipschitzWith.id.const_max a).const_min b
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc := hclip.dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
  change |averagingRamp a b x - averagingRamp a b y| ≤ (1 / (b - a)) * |x - y|
  have heq : averagingRamp a b x - averagingRamp a b y =
      (min b (max a x) - min b (max a y)) / (b - a) := by unfold averagingRamp; ring
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hab), one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right hc (sub_pos.mpr hab).le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampLocalLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the sharp local law to a ramp cutoff -/

namespace JointDickman

open MeasureTheory Finset

open Classical in
theorem intervalIntegrable_strict_cutoff (x a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => if t < x then (1 : ℝ) else 0) volume a b := by
  have h := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b)
  have heq : (Set.Iio x).indicator (fun _ : ℝ => (1 : ℝ)) =
      (fun t => if t < x then (1 : ℝ) else 0) := by
    funext t
    rfl
  rw [← heq]
  exact intervalIntegrable_iff.mpr (h.def'.indicator measurableSet_Iio)

open Classical in
theorem highExclusiveCell_intervalIntegrable {C E A : Type*} [Fintype E] [DecidableEq A]
    (v : E → ℝ) (cell : C → E → Option A) (location : E → ℝ)
    (c : C) (a : A) (lo hi : ℝ) :
    IntervalIntegrable
      (fun t => highExclusiveCell v cell (fun e => location e ≤ t) c a) volume lo hi := by
  simp only [highExclusiveCell_eq_sum, not_le]
  have hs : IntervalIntegrable (∑ e : E, fun t =>
      if t < location e ∧ cell c e = some a then v e else 0) volume lo hi := by
    apply IntervalIntegrable.sum
    intro e _
    by_cases he : cell c e = some a
    · simpa only [he, and_true, mul_ite, mul_one, mul_zero] using
        (intervalIntegrable_strict_cutoff (location e) lo hi).const_mul (v e)
    · simp only [he, and_false, ↓reduceIte]
      exact intervalIntegrable_const
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  exact (Finset.sum_apply t Finset.univ
    (fun e : E => fun s : ℝ => if s < location e ∧ cell c e = some a then v e else 0)).symm

open Classical in
/-- The linear ramp is exactly an average of sharp high cutoffs. -/
theorem rampCellMass_eq_average {C E A : Type*} [Fintype E] [DecidableEq A]
    (v : E → ℝ) (cell : C → E → Option A) (location : E → ℝ)
    (c : C) (a : A) {lo hi : ℝ} (hlohi : lo < hi) :
    optionCellMass (fun e => v e * averagingRamp lo hi (location e)) (cell c) a =
      (∫ t in lo..hi, highExclusiveCell v cell (fun e => location e ≤ t) c a) / (hi - lo) := by
  simp only [highExclusiveCell_eq_sum, not_le]
  rw [intervalIntegral.integral_finsetSum]
  · unfold optionCellMass
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : cell c e = some a
    · simp only [he, and_true, ↓reduceIte]
      rw [averagingRamp_integral hlohi]
      have heq : (fun t => if t < location e then v e else 0) =
          (fun t => v e * (if t < location e then 1 else 0)) := by funext t; split_ifs <;> simp
      rw [heq, intervalIntegral.integral_const_mul]
      ring
    · simp [he]
  · intro e _
    by_cases he : cell c e = some a
    · simpa only [he, and_true, mul_ite, mul_one, mul_zero] using
        (intervalIntegrable_strict_cutoff (location e) lo hi).const_mul (v e)
    · simp only [he, and_false, ↓reduceIte]
      exact intervalIntegrable_const

open Classical in
/-- Averaging a pointwise local error keeps the same error constant. -/
theorem rampCellMass_local_error {C E A : Type*} [Fintype E] [DecidableEq A]
    (v : E → ℝ) (cell : C → E → Option A) (location : E → ℝ)
    (c : C) (a : A) {lo hi ε : ℝ} (hlohi : lo < hi) (profile : ℝ → ℝ)
    (hprofile : IntervalIntegrable profile volume lo hi)
    (herror : ∀ t ∈ Set.Icc lo hi,
      |highExclusiveCell v cell (fun e => location e ≤ t) c a - profile t| ≤ ε) :
    |optionCellMass (fun e => v e * averagingRamp lo hi (location e)) (cell c) a -
      (∫ t in lo..hi, profile t) / (hi - lo)| ≤ ε := by
  rw [rampCellMass_eq_average v cell location c a hlohi, ← sub_div,
    ← intervalIntegral.integral_sub
      (highExclusiveCell_intervalIntegrable v cell location c a lo hi) hprofile]
  rw [abs_div, abs_of_pos (sub_pos.mpr hlohi)]
  apply (div_le_iff₀ (sub_pos.mpr hlohi)).mpr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := lo) (b := hi) (f := fun t =>
      highExclusiveCell v cell (fun e => location e ≤ t) c a - profile t)
    (C := ε) (fun t ht => by
      rw [Real.norm_eq_abs]
      exact herror t (Set.uIcc_of_le hlohi.le ▸ Set.uIoc_subset_uIcc ht))
  simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hlohi)] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ClippedProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity of the clipped local-law profile -/

namespace JointDickman

open MeasureTheory Set

open Classical in
theorem clippedIntervalIntegral_eq_clamp (f : ℝ → ℝ) (θ a b t : ℝ) :
    clippedIntervalIntegral f θ a b t = ∫ s in min (b - t) (max θ (a - t))..b - t, f s := by
  unfold clippedIntervalIntegral
  by_cases h : max θ (a - t) ≤ b - t
  · rw [ite_eq_left h, min_eq_right h]
  · rw [ite_eq_right h, min_eq_left (le_of_not_ge h)]
    simp

open Classical in
theorem clippedIntervalIntegral_continuousOn (f : ℝ → ℝ) {lo hi : ℝ}
    (hf : ContinuousOn f (Ici lo)) (a b t : ℝ) :
    ContinuousOn (fun θ => clippedIntervalIntegral f θ a b t) (Icc lo hi) := by
  by_cases hb : lo ≤ b - t
  · have hfi : IntegrableOn f (uIcc lo (b - t)) volume := by
      rw [uIcc_of_le hb]
      exact (hf.mono (fun _ hx => hx.1)).integrableOn_Icc
    have hp := intervalIntegral.continuousOn_primitive_interval_left hfi
    have hc : Continuous (fun θ : ℝ => min (b - t) (max θ (a - t))) :=
      continuous_const.min (continuous_id.max continuous_const)
    have hm : MapsTo (fun θ : ℝ => min (b - t) (max θ (a - t))) (Icc lo hi)
        (uIcc lo (b - t)) := by
      intro θ hθ
      rw [uIcc_of_le hb]
      exact ⟨le_min hb (hθ.1.trans (le_max_left _ _)), min_le_left _ _⟩
    exact (hp.comp hc.continuousOn hm).congr
      (fun θ _ => clippedIntervalIntegral_eq_clamp f θ a b t)
  · apply (continuousOn_const (c := (0 : ℝ))).congr
    intro θ hθ
    unfold clippedIntervalIntegral
    have h : ¬max θ (a - t) ≤ b - t := by
      intro he
      exact hb (hθ.1.trans ((le_max_left _ _).trans he))
    exact ite_eq_right h

open Classical in
theorem scaledClippedProfile_intervalIntegrable (v : ℕ → ℝ) (z : ℝ) (H B : ℕ)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) (a b t : ℝ) :
    IntervalIntegrable
      (fun θ => clippedIntervalIntegral (scaledRoughDensity v z H B) θ a b t)
      volume lo hi := by
  have hc : ContinuousOn (scaledRoughDensity v z H B) (Ici lo) := by
    intro s hs
    exact (hasDerivAt_scaledRoughDensity v z H B (hlo.trans_le hs)).continuousAt.continuousWithinAt
  exact (clippedIntervalIntegral_continuousOn _ hc a b t).intervalIntegrable_of_Icc hlohi

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeRampLocalLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual prime-product local law with a ramp weight -/

namespace JointDickman

open Filter MeasureTheory
open scoped Topology

open Classical in
/-- The sharp published-input consequence survives averaging the cutoff,
with the same error and uniformity in the finite partition. -/
theorem primeRampCell_local_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ v : ℕ → ℝ, v 0 = squarefreeLeadingConstant (1 / 4) ∧ 0 < v 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ lo hi : ℝ, (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ lo → lo < hi →
        ∀ lower upper : D → ℝ,
        (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
        (∀ d, upper d ≤ 16 / 5) → ∀ c : auxiliaryPrimes B → Bool, ∀ d : D, ∀ r : (ZMod q)ˣ,
        |optionCellMass
            (fun e => quarterPrimeMass (auxiliaryPrimes B) e *
              averagingRamp lo hi (Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B))
            (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper) c) (d, r) -
          rampIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
            lo hi (lower d) (upper d)
            (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨v, hv, hvpos, H, C, hC, hbound⟩ := highExclusiveLogCell_threshold_law hSD hSW hM
  refine ⟨v, hv, hvpos, H, C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro D _ q _ hq lo hi hlo hlohi lower upper hdisjoint hupper c d r
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hlopos : 0 < lo := (Real.rpow_pos_of_pos hBpos _).trans_le hlo
  have hip := (scaledClippedProfile_intervalIntegrable v (1 / 4) H B
    hlopos hlohi.le (lower d) (upper d)
    (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)).div_const (q.totient : ℝ)
  have herr := rampCellMass_local_error
    (quarterPrimeMass (auxiliaryPrimes B))
    (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper))
    (fun e => Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B)
    c (d, r) hlohi _ hip (fun θ hθ =>
      hboundB D q hq θ (hlo.trans hθ.1) lower upper hdisjoint hupper c d r)
  simpa only [rampIntervalIntegral, intervalIntegral.integral_div, div_div, mul_comm] using herr

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampDensityIntegral
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The averaged profile is the integral of the ramp-weighted density -/

namespace JointDickman

open MeasureTheory Set

open Classical in
theorem clippedIntervalIntegral_eq_indicator (f : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (θ : ℝ) :
    clippedIntervalIntegral f θ a b 0 = ∫ s in a..b, if θ < s then f s else 0 := by
  have heq : (fun s => if θ < s then f s else 0) = (Ioi θ).indicator f := by
    funext s
    rfl
  rw [heq, intervalIntegral.integral_of_le hab, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, inter_comm, Ioc_inter_Ioi]
  unfold clippedIntervalIntegral
  simp only [sub_zero]
  by_cases h : max θ a ≤ b
  · rw [ite_eq_left h, intervalIntegral.integral_of_le h, max_comm]
  · rw [ite_eq_right h]
    have hempty : Ioc (max a θ) b = ∅ := Ioc_eq_empty_of_le (by simpa [max_comm] using (le_of_not_ge h))
    rw [hempty]
    simp

open Classical in
theorem indicator_density_rectangle_integrable (f : ℝ → ℝ) (hf : Continuous f)
    (lo hi a b : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => if p.1 < p.2 then f p.2 else 0)
      (uIoc lo hi ×ˢ uIoc a b) := by
  have hbase : IntegrableOn (fun p : ℝ × ℝ => f p.2) (uIcc lo hi ×ˢ uIcc a b) :=
    (hf.comp continuous_snd).continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have hsmall := hbase.mono_set (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
  have h := hsmall.indicator hset
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rfl

open Classical in
/-- Fubini converts the average of sharp tails to the desired weighted
Lebesgue integral. Only ordinary continuity of the density is needed. -/
theorem rampIntervalIntegral_eq_density (f : ℝ → ℝ) (hf : Continuous f)
    {lo hi a b : ℝ} (hlohi : lo < hi) (hab : a ≤ b) :
    rampIntervalIntegral f lo hi a b 0 =
      ∫ s in a..b, averagingRamp lo hi s * f s := by
  unfold rampIntervalIntegral
  have hsharp : (fun θ => clippedIntervalIntegral f θ a b 0) =
      (fun θ => ∫ s in a..b, if θ < s then f s else 0) := by
    funext θ
    exact clippedIntervalIntegral_eq_indicator f hab θ
  rw [hsharp, intervalIntegral_intervalIntegral_swap (F := fun θ s => if θ < s then f s else 0)
    (a := lo) (b := hi) (c := a) (d := b) (indicator_density_rectangle_integrable f hf lo hi a b)]
  have hin (s : ℝ) : (∫ θ in lo..hi, if θ < s then f s else 0) =
      (hi - lo) * (averagingRamp lo hi s * f s) := by
    have heq : (fun θ => if θ < s then f s else 0) =
        (fun θ => (if θ < s then (1 : ℝ) else 0) * f s) := by
      funext θ
      split_ifs <;> simp
    rw [heq, intervalIntegral.integral_mul_const, integral_strict_cutoff hlohi.le]
    unfold averagingRamp
    field_simp [(sub_pos.mpr hlohi).ne']
  simp_rw [hin]
  rw [intervalIntegral.integral_const_mul]
  exact mul_div_cancel_left₀ _ (sub_pos.mpr hlohi).ne'

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded Lipschitz densities after the lower ramp cutoff -/

namespace JointDickman

open scoped NNReal

theorem rampDensity_bound (f : ℝ → ℝ) {lo hi M : ℝ} (hlohi : lo < hi)
    (hbound : ∀ x ∈ Set.Ici lo, |f x| ≤ M) (x : ℝ) :
    |rampDensity f lo hi x| ≤ M := by
  have hr := averagingRamp_bounds hlohi x
  have hf := hbound (max lo x) (Set.mem_Ici.mpr (le_max_left _ _))
  rw [rampDensity, abs_mul, abs_of_nonneg hr.1]
  exact (mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)).trans (by simpa using hf)

theorem clampedDensity_lipschitz (f : ℝ → ℝ) {lo : ℝ} {L : ℝ≥0}
    (hLip : LipschitzOnWith L f (Set.Ici lo)) :
    LipschitzWith L (fun x => f (max lo x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hLip.dist_le_mul (max lo x) (Set.mem_Ici.mpr (le_max_left lo x))
    (max lo y) (Set.mem_Ici.mpr (le_max_left lo y))
  have hm : dist (max lo x) (max lo y) ≤ dist x y := by
    simpa only [id_eq, NNReal.coe_one, one_mul] using (LipschitzWith.id.const_max lo).dist_le_mul x y
  exact h.trans (mul_le_mul_of_nonneg_left hm L.coe_nonneg)

theorem rampDensity_lipschitz (f : ℝ → ℝ) {lo hi : ℝ} {M L : ℝ≥0}
    (hlohi : lo < hi) (hbound : ∀ x ∈ Set.Ici lo, |f x| ≤ M)
    (hLip : LipschitzOnWith L f (Set.Ici lo)) :
    LipschitzWith ⟨(L : ℝ) + (1 / (hi - lo)) * (M : ℝ), by positivity⟩ (rampDensity f lo hi) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hrx := averagingRamp_bounds hlohi x
  have hrd := (averagingRamp_lipschitz hlohi).dist_le_mul x y
  have hfd := (clampedDensity_lipschitz f hLip).dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq] at hrd hfd
  have hfy := hbound (max lo y) (Set.mem_Ici.mpr (le_max_left _ _))
  change |rampDensity f lo hi x - rampDensity f lo hi y| ≤
    ((L : ℝ) + (1 / (hi - lo)) * (M : ℝ)) * |x - y|
  calc
    _ = |averagingRamp lo hi x * (f (max lo x) - f (max lo y)) +
      (averagingRamp lo hi x - averagingRamp lo hi y) * f (max lo y)| := by
        unfold rampDensity
        congr 1
        ring
    _ ≤ |averagingRamp lo hi x * (f (max lo x) - f (max lo y))| +
      |(averagingRamp lo hi x - averagingRamp lo hi y) * f (max lo y)| := abs_add_le _ _
    _ ≤ (L : ℝ) * |x - y| + ((1 / (hi - lo)) * |x - y|) * M := by
      rw [abs_mul, abs_mul, abs_of_nonneg hrx.1]
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_right hrx.2 (abs_nonneg _)).trans (by simpa using hfd)
      · exact mul_le_mul hrd hfy (abs_nonneg _) (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the smoothed local-law profile -/

namespace JointDickman

open MeasureTheory Set
open scoped NNReal

open Classical in
theorem clippedIntervalIntegral_congr_above (f g : ℝ → ℝ) {lo θ : ℝ}
    (hθ : lo ≤ θ) (hfg : ∀ s ∈ Ici lo, f s = g s) (a b t : ℝ) :
    clippedIntervalIntegral f θ a b t = clippedIntervalIntegral g θ a b t := by
  unfold clippedIntervalIntegral
  split_ifs with hab
  · apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact hfg s (hθ.trans ((le_max_left _ _).trans hs.1))
  · rfl

open Classical in
theorem rampIntervalIntegral_eq_rampDensity (f : ℝ → ℝ) {lo hi : ℝ} {L : ℝ≥0}
    (hlohi : lo < hi) (hLip : LipschitzOnWith L f (Ici lo))
    {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    rampIntervalIntegral f lo hi a b t =
      ∫ x in a..b, rampDensity f lo hi (x - t) := by
  let g : ℝ → ℝ := fun s => f (max lo s)
  have hg : Continuous g := (clampedDensity_lipschitz f hLip).continuous
  have heq : rampIntervalIntegral f lo hi a b t =
      rampIntervalIntegral g lo hi (a - t) (b - t) 0 := by
    unfold rampIntervalIntegral
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hlohi.le] at hθ
    have hc := clippedIntervalIntegral_congr_above f g hθ.1
      (fun s hs => by simp only [g, max_eq_right (Set.mem_Ici.mp hs)]) a b t
    simpa only [clippedIntervalIntegral, sub_zero] using hc
  rw [heq, rampIntervalIntegral_eq_density g hg hlohi (sub_le_sub_right hab t)]
  rw [intervalIntegral.integral_comp_sub_right]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PublishedRampProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smoothed prime channel profile from published inputs -/

namespace JointDickman

open Filter MeasureTheory
open scoped Topology NNReal

open Classical in
/-- Uniform bounded Lipschitz profiles and their actual weighted cell law.
The constants may depend on the fixed ramp, never on the partition or B. -/
theorem primeRampProfile_from_published_jd_oai
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ v : ℕ → ℝ, v 0 = squarefreeLeadingConstant (1 / 4) ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ lo hi : ℝ, 0 < lo → lo < hi →
      ∃ M L : ℝ≥0, ∀ᶠ B : ℕ in atTop,
        (∀ x, |rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi x| ≤ M) ∧
        LipschitzWith L (rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi) ∧
        ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ lower upper : D → ℝ,
        (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
        (∀ d, lower d < upper d) → (∀ d, upper d ≤ 16 / 5) →
        ∀ c : auxiliaryPrimes B → Bool, ∀ d : D, ∀ r : (ZMod q)ˣ,
        |primeRampCell B q lower upper lo hi c (d, r) -
          (∫ x in lower d..upper d,
            rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi
              (x - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨v, hv, _, H, C, hC, hlocal⟩ := primeRampCell_local_law hSD hSW hM
  refine ⟨v, hv, H, C, hC, ?_⟩
  intro lo hi hlo hlohi
  obtain ⟨M, hM0, L, hbound⟩ := scaledRoughDensity_bounded_lipschitz hM hMP v hv
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) hlo H
  let M₀ : ℝ≥0 := ⟨M, hM0⟩
  let L₀ : ℝ≥0 := ⟨(L : ℝ) + (1 / (hi - lo)) * (M₀ : ℝ), by positivity⟩
  refine ⟨M₀, L₀, ?_⟩
  have hsmall : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ lo := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
    exact (ht.eventually (eventually_lt_nhds hlo)).mono (fun _ h => h.le)
  filter_upwards [hlocal, hbound, hsmall] with B hlocalB hboundB hsmallB
  refine ⟨rampDensity_bound _ hlohi hboundB.1,
    rampDensity_lipschitz _ hlohi hboundB.1 hboundB.2, ?_⟩
  intro D _ q _ hq lower upper hdisjoint horder hupper c d r
  have hh := hlocalB D q hq lo hi hsmallB hlohi lower upper hdisjoint hupper c d r
  rw [rampIntervalIntegral_eq_rampDensity _ hlohi hboundB.2 (horder d).le] at hh
  exact hh

end JointDickman

end OAI
end

theorem solution.{u_1} : type_of% @OAI.JointDickman.primeRampProfile_from_published_jd_oai.{u_1} := @OAI.JointDickman.primeRampProfile_from_published_jd_oai.{u_1}
