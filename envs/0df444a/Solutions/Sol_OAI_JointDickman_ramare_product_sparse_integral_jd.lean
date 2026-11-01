-- Prove2me | solution 1 for OAI.JointDickman.ramare_product_sparse_integral_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:56:43.148276+00:00
-- url     : https://prove2.me/submissions/8877ddfd-2c23-447a-85fa-f270a8043aa5

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002
import Theorems.Thm_OAI_JointDickman_mellin_prime_sampling_arithmetic_jd
import Theorems.Thm_OAI_JointDickman_primeProductMertensInput_jd

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_DiscreteFirstDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.ExponentialSum

lemma phase_norm (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cot_antitone_unit {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    Real.cot (Real.pi * y) ≤ Real.cot (Real.pi * x) := by
  have hpi := Real.pi_pos
  have hxpi : 0 < Real.pi * x := mul_pos hpi hx
  have hypi : 0 < Real.pi * y := by nlinarith
  have hxpi' : Real.pi * x < Real.pi := by nlinarith
  have hypi' : Real.pi * y < Real.pi := by nlinarith
  have hsx := Real.sin_pos_of_pos_of_lt_pi hxpi hxpi'
  have hsy := Real.sin_pos_of_pos_of_lt_pi hypi hypi'
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  apply (div_le_div_iff₀ hsy hsx).2
  have hs : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> nlinarith
  rw [Real.sin_sub] at hs
  nlinarith

lemma sin_pi_lower {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    2 * β ≤ Real.sin (Real.pi * x) := by
  have hp := Real.pi_pos
  by_cases hx : x ≤ 1 / 2
  · have h := Real.mul_le_sin (x := Real.pi * x) (by nlinarith) (by nlinarith)
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at h
    linarith
  · have h := Real.mul_le_sin (x := Real.pi * (1 - x)) (by nlinarith) (by nlinarith)
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq] at h
    have harg : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
    rw [harg, Real.sin_pi_sub] at h
    linarith

lemma abs_cot_pi_le {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    |Real.cot (Real.pi * x)| ≤ 1 / (2 * β) := by
  have hs := sin_pi_lower hβ hlo hhi
  have hsp : 0 < Real.sin (Real.pi * x) := by linarith
  rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsp]
  exact (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hsp.le).trans
    (one_div_le_one_div_of_le (by positivity) hs)

lemma phaseWeight_identity {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (phase x - 1) * phaseWeight x = 1 := by
  have hs : Real.sin (Real.pi * x) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos]))
  unfold phase phaseWeight
  rw [Complex.exp_ofReal_mul_I]
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
  rw [Real.sin_two_mul, Real.cos_two_mul, Real.cot_eq_cos_div_sin]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_div]
  have hsc : (Real.sin (Real.pi * x) : ℂ) ^ 2 + (Real.cos (Real.pi * x) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (Real.pi * x)
  have hsC : (Real.sin (Real.pi * x) : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp
  ring_nf
  norm_num only [Complex.ofReal_one, Complex.I_sq]
  linear_combination -2 * (Real.cos (Real.pi * x) : ℂ) * Complex.I * hsc

lemma phaseWeight_norm_le {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    ‖phaseWeight x‖ ≤ 1 / 2 + 1 / (4 * β) := by
  have hc := abs_cot_pi_le hβ hlo hhi
  have hn2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  calc
    ‖phaseWeight x‖ ≤ ‖-(1 : ℂ) / 2‖ + ‖(Real.cot (Real.pi * x) : ℂ) * Complex.I / 2‖ :=
      norm_sub_le _ _
    _ = 1 / 2 + |Real.cot (Real.pi * x)| / 2 := by
      simp only [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, hn2, mul_one]
    _ ≤ 1 / 2 + (1 / (2 * β)) / 2 := by gcongr
    _ = 1 / 2 + 1 / (4 * β) := by ring

lemma phaseWeight_difference_norm {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    ‖phaseWeight x - phaseWeight y‖ =
      (Real.cot (Real.pi * x) - Real.cot (Real.pi * y)) / 2 := by
  have hc := cot_antitone_unit hx hxy hy
  have heq : phaseWeight x - phaseWeight y =
      (((Real.cot (Real.pi * x) - Real.cot (Real.pi * y)) / 2 : ℝ) : ℂ) * (-Complex.I) := by
    unfold phaseWeight
    push_cast
    ring
  rw [heq, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

lemma phase_step_weight (f : ℕ → ℝ) (i : ℕ)
    (hlo : 0 < f (i + 1) - f i) (hhi : f (i + 1) - f i < 1) :
    (phase (f (i + 1)) - phase (f i)) * phaseWeight (f (i + 1) - f i) = phase (f i) := by
  have heq : phase (f (i + 1)) = phase (f i) * phase (f (i + 1) - f i) := by
    rw [← phase_add]
    congr 1
    ring
  rw [heq]
  calc
    (phase (f i) * phase (f (i + 1) - f i) - phase (f i)) *
        phaseWeight (f (i + 1) - f i) =
      phase (f i) * ((phase (f (i + 1) - f i) - 1) * phaseWeight (f (i + 1) - f i)) := by ring
    _ = phase (f i) := by rw [phaseWeight_identity hlo hhi, mul_one]

/-- Summation by parts for a sequence whose differences have a reciprocal weight. -/
lemma weighted_telescope (z w : ℕ → ℂ) (N : ℕ)
    (hstep : ∀ i < N, (z (i + 1) - z i) * w i = z i) :
    (∑ i ∈ Finset.range N, z i) = z N * w N - z 0 * w 0 +
      ∑ i ∈ Finset.range N, z (i + 1) * (w i - w (i + 1)) := by
  calc
    (∑ i ∈ Finset.range N, z i) =
        ∑ i ∈ Finset.range N,
          ((z (i + 1) * w (i + 1) - z i * w i) + z (i + 1) * (w i - w (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hstep i (Finset.mem_range.mp hi)
      linear_combination -h
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun i => z i * w i)]

/-- Endpoint-efficient form: the last weight is attached to the last summand. -/
lemma weighted_telescope_succ (z w : ℕ → ℂ) (N : ℕ)
    (hstep : ∀ i ≤ N, (z (i + 1) - z i) * w i = z i) :
    (∑ i ∈ Finset.range (N + 1), z i) = z (N + 1) * w N - z 0 * w 0 +
      ∑ i ∈ Finset.range N, z (i + 1) * (w i - w (i + 1)) := by
  rw [Finset.sum_range_succ, weighted_telescope z w N (fun i hi => hstep i hi.le)]
  have h := hstep N le_rfl
  linear_combination -h

/-- A discrete first-derivative estimate (Kusmin--Landau): monotone consecutive
phase increments, uniformly separated from the integers, force cancellation.
The last increment is included to make the endpoint formula uniform, including `N=0`. -/
theorem first_derivative_sum_bound (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hlo : ∀ i ≤ N, β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range N, phase (f i)‖ ≤ 2 / β := by
  let d : ℕ → ℝ := fun i => f (i + 1) - f i
  let w : ℕ → ℂ := fun i => phaseWeight (d i)
  have hdlo : ∀ i ≤ N, 0 < d i := fun i hi => lt_of_lt_of_le hβ (hlo i hi)
  have hdhi : ∀ i ≤ N, d i < 1 := by intro i hi; have := hhi i hi; dsimp [d] <;> linarith
  have htel := weighted_telescope (fun i => phase (f i)) w N (by
    intro i hi
    exact phase_step_weight f i (hdlo i hi.le) (hdhi i hi.le))
  have hvariation : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
      (Real.cot (Real.pi * d 0) - Real.cot (Real.pi * d N)) / 2 := by
    calc
      (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
          ∑ i ∈ Finset.range N,
            (Real.cot (Real.pi * d i) - Real.cot (Real.pi * d (i + 1))) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i < N := Finset.mem_range.mp hi
        exact phaseWeight_difference_norm (hdlo i hiN.le)
          (hmono (show i ≤ N from hiN.le) (show i + 1 ≤ N by omega) (by omega)) (hdhi (i + 1) (by omega))
      _ = _ := by rw [← Finset.sum_div, Finset.sum_range_sub']
  have hc0 := abs_cot_pi_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hcN := abs_cot_pi_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hvbound : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) ≤ 1 / (2 * β) := by
    rw [hvariation]
    have h0 := (abs_le.mp hc0).2
    have hN := (abs_le.mp hcN).1
    change Real.cot (Real.pi * d 0) ≤ _ at h0
    change _ ≤ Real.cot (Real.pi * d N) at hN
    linarith
  have hw0 := phaseWeight_norm_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hwN := phaseWeight_norm_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hsum : ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ ≤
      ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range N, ‖phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, phase_norm, one_mul]
  have hβle : β ≤ 1 := by have := hlo 0 (Nat.zero_le N); have := hhi 0 (Nat.zero_le N); linarith
  have hinv : 1 ≤ 1 / β := (le_div_iff₀ hβ).2 (by simpa using hβle)
  rw [htel]
  calc
    _ ≤ ‖phase (f N) * w N - phase (f 0) * w 0‖ +
        ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_add_le _ _
    _ ≤ (‖phase (f N) * w N‖ + ‖phase (f 0) * w 0‖) +
        ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := add_le_add (norm_sub_le _ _) hsum
    _ = (‖w N‖ + ‖w 0‖) + ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
      simp only [norm_mul, phase_norm, one_mul]
    _ ≤ (1 / 2 + 1 / (4 * β)) + (1 / 2 + 1 / (4 * β)) + 1 / (2 * β) := by
      exact add_le_add (add_le_add hwN hw0) hvbound
    _ = 1 + 1 / β := by ring
    _ ≤ 1 / β + 1 / β := by simpa [add_comm] using add_le_add_right hinv (1 / β)
    _ = 2 / β := by ring

/-- Cancellation using only the increments attached to the summands. -/
theorem first_derivative_sum_bound_succ (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hlo : ∀ i ≤ N, β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range (N + 1), phase (f i)‖ ≤ 2 / β := by
  let d : ℕ → ℝ := fun i => f (i + 1) - f i
  let w : ℕ → ℂ := fun i => phaseWeight (d i)
  have hdlo : ∀ i ≤ N, 0 < d i := fun i hi => lt_of_lt_of_le hβ (hlo i hi)
  have hdhi : ∀ i ≤ N, d i < 1 := by intro i hi; have := hhi i hi; dsimp [d] <;> linarith
  have htel := weighted_telescope_succ (fun i => phase (f i)) w N (by
    intro i hi
    exact phase_step_weight f i (hdlo i hi) (hdhi i hi))
  have hvariation : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
      (Real.cot (Real.pi * d 0) - Real.cot (Real.pi * d N)) / 2 := by
    calc
      (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
          ∑ i ∈ Finset.range N,
            (Real.cot (Real.pi * d i) - Real.cot (Real.pi * d (i + 1))) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i < N := Finset.mem_range.mp hi
        exact phaseWeight_difference_norm (hdlo i hiN.le)
          (hmono (show i ≤ N from hiN.le) (show i + 1 ≤ N by omega) (by omega)) (hdhi (i + 1) (by omega))
      _ = _ := by rw [← Finset.sum_div, Finset.sum_range_sub']
  have hc0 := abs_cot_pi_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hcN := abs_cot_pi_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hvbound : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) ≤ 1 / (2 * β) := by
    rw [hvariation]
    have h0 := (abs_le.mp hc0).2
    have hN := (abs_le.mp hcN).1
    change Real.cot (Real.pi * d 0) ≤ _ at h0
    change _ ≤ Real.cot (Real.pi * d N) at hN
    linarith
  have hw0 := phaseWeight_norm_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hwN := phaseWeight_norm_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hsum : ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ ≤
      ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range N, ‖phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, phase_norm, one_mul]
  have hβle : β ≤ 1 := by have := hlo 0 (Nat.zero_le N); have := hhi 0 (Nat.zero_le N); linarith
  have hinv : 1 ≤ 1 / β := (le_div_iff₀ hβ).2 (by simpa using hβle)
  rw [htel]
  calc
    _ ≤ ‖phase (f (N + 1)) * w N - phase (f 0) * w 0‖ +
        ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_add_le _ _
    _ ≤ (‖phase (f (N + 1)) * w N‖ + ‖phase (f 0) * w 0‖) +
        ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := add_le_add (norm_sub_le _ _) hsum
    _ = (‖w N‖ + ‖w 0‖) + ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
      simp only [norm_mul, phase_norm, one_mul]
    _ ≤ (1 / 2 + 1 / (4 * β)) + (1 / 2 + 1 / (4 * β)) + 1 / (2 * β) := by
      exact add_le_add (add_le_add hwN hw0) hvbound
    _ = 1 + 1 / β := by ring
    _ ≤ 1 / β + 1 / β := by simpa [add_comm] using add_le_add_right hinv (1 / β)
    _ = 2 / β := by ring

lemma phase_int (q : ℤ) : phase (q : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I q using 2
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

lemma phase_neg (x : ℝ) : phase (-x) = (starRingEnd ℂ) (phase x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma phase_sub_int_mul (x : ℝ) (q : ℤ) (n : ℕ) :
    phase (x - (q : ℝ) * n) = phase x := by
  have heq : x - (q : ℝ) * n = x + ((-(q * (n : ℤ)) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [heq, phase_add, phase_int, mul_one]

/-- Integer translations of the increment strip do not affect the estimate. -/
theorem first_derivative_sum_bound_strip (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (q : ℤ)
    (hβ : 0 < β)
    (hlo : ∀ i ≤ N, (q : ℝ) + β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range N, phase (f i)‖ ≤ 2 / β := by
  let g : ℕ → ℝ := fun i => f i - (q : ℝ) * i
  have hg : ∀ i, g (i + 1) - g i = (f (i + 1) - f i) - q := by
    intro i
    dsimp [g]
    push_cast
    ring
  have H := first_derivative_sum_bound g N β hβ
    (by intro i hi; rw [hg]; have := hlo i hi; linarith)
    (by intro i hi; rw [hg]; have := hhi i hi; linarith)
    (by
      intro i hi j hj hij
      dsimp only
      rw [hg, hg]
      exact sub_le_sub_right (hmono hi hj hij) _)
  simpa only [g, phase_sub_int_mul] using H

theorem first_derivative_sum_bound_strip_succ (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (q : ℤ)
    (hβ : 0 < β)
    (hlo : ∀ i ≤ N, (q : ℝ) + β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range (N + 1), phase (f i)‖ ≤ 2 / β := by
  let g : ℕ → ℝ := fun i => f i - (q : ℝ) * i
  have hg : ∀ i, g (i + 1) - g i = (f (i + 1) - f i) - q := by
    intro i
    dsimp [g]
    push_cast
    ring
  have H := first_derivative_sum_bound_succ g N β hβ
    (by intro i hi; rw [hg]; have := hlo i hi; linarith)
    (by intro i hi; rw [hg]; have := hhi i hi; linarith)
    (by
      intro i hi j hj hij
      dsimp only
      rw [hg, hg]
      exact sub_le_sub_right (hmono hi hj hij) _)
  simpa only [g, phase_sub_int_mul] using H

/-- Both directions of monotonicity are allowed in the discrete
first-derivative estimate. -/
theorem first_derivative_sum_bound_either_succ (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (q : ℤ)
    (hβ : 0 < β)
    (hlo : ∀ i ≤ N, (q : ℝ) + β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N) ∨
      AntitoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range (N + 1), phase (f i)‖ ≤ 2 / β := by
  rcases hmono with hmono | hanti
  · exact first_derivative_sum_bound_strip_succ f N β q hβ hlo hhi hmono
  · have H := first_derivative_sum_bound_strip_succ (fun i => -f i) N β (-q - 1) hβ
      (by intro i hi; push_cast; have := hhi i hi; linarith)
      (by intro i hi; push_cast; have := hlo i hi; linarith)
      (by
        intro i hi j hj hij
        have := hanti hi hj hij
        dsimp only
        linarith)
    simpa only [phase_neg, ← map_sum, Complex.norm_conj] using H

/-- The first-derivative bound on a contiguous block of natural indices. -/
theorem first_derivative_sum_bound_Icc (f : ℕ → ℝ) (a b : ℕ) (β : ℝ) (q : ℤ)
    (hβ : 0 < β)
    (hlo : ∀ i, a ≤ i → i ≤ b → (q : ℝ) + β ≤ f (i + 1) - f i)
    (hhi : ∀ i, a ≤ i → i ≤ b → f (i + 1) - f i ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Icc a b) ∨
      AntitoneOn (fun i => f (i + 1) - f i) (Set.Icc a b)) :
    ‖∑ i ∈ Finset.Icc a b, phase (f i)‖ ≤ 2 / β := by
  by_cases hab : a ≤ b
  · have H := first_derivative_sum_bound_either_succ (fun i => f (a + i)) (b - a) β q hβ
      (by
        intro i hi
        simpa only [Nat.add_assoc] using hlo (a + i) (by omega) (by omega))
      (by
        intro i hi
        simpa only [Nat.add_assoc] using hhi (a + i) (by omega) (by omega))
      (by
        rcases hmono with hm | hm
        · left
          intro i hi j hj hij
          dsimp only
          simpa only [Nat.add_assoc] using hm
            (show a + i ∈ Set.Icc a b by constructor <;> simp only [Set.mem_Iic] at hi hj <;> omega)
            (show a + j ∈ Set.Icc a b by constructor <;> simp only [Set.mem_Iic] at hi hj <;> omega)
            (show a + i ≤ a + j by omega)
        · right
          intro i hi j hj hij
          dsimp only
          simpa only [Nat.add_assoc] using hm
            (show a + i ∈ Set.Icc a b by constructor <;> simp only [Set.mem_Iic] at hi hj <;> omega)
            (show a + j ∈ Set.Icc a b by constructor <;> simp only [Set.mem_Iic] at hi hj <;> omega)
            (show a + i ≤ a + j by omega))
    have hset : Finset.Icc a b = Finset.Ico a (b + 1) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    have hlen : b + 1 - a = b - a + 1 := by omega
    rw [hlen]
    exact H
  · have he : Finset.Icc a b = ∅ := Finset.Icc_eq_empty (by omega)
    rw [he]
    simp only [Finset.sum_empty, norm_zero]
    positivity

end Problem337.ExponentialSum

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_MonotoneBlocks
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- The indices of a monotone sequence lying in a closed interval form one
possibly empty interval of indices. -/
theorem monotone_filter_range_eq_Ico {α : Type*} [LinearOrder α]
    (d : ℕ → α) (hd : Monotone d) (N : ℕ) (L R : α) :
    ∃ a b : ℕ, a ≤ b ∧ b ≤ N ∧
      (Finset.range N).filter (fun j => L ≤ d j ∧ d j ≤ R) = Finset.Ico a b := by
  classical
  let s := (Finset.range N).filter (fun j => L ≤ d j ∧ d j ≤ R)
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have ha : a ∈ s := Finset.min'_mem _ hs
    have hb : b ∈ s := Finset.max'_mem _ hs
    have hab : a ≤ b := Finset.min'_le _ _ hb
    have hbN : b < N := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    refine ⟨a, b + 1, by omega, by omega, ?_⟩
    change s = Finset.Ico a (b + 1)
    ext j
    constructor
    · intro hj
      exact Finset.mem_Ico.mpr ⟨Finset.min'_le _ _ hj, Nat.lt_succ_iff.mpr (Finset.le_max' _ _ hj)⟩
    · intro hj
      rcases Finset.mem_Ico.mp hj with ⟨haj, hjb⟩
      have hjb' : j ≤ b := Nat.lt_succ_iff.mp hjb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hjb' hbN), ?_⟩
      exact ⟨(Finset.mem_filter.mp ha).2.1.trans (hd haj),
        (hd hjb').trans (Finset.mem_filter.mp hb).2.2⟩
  · refine ⟨0, 0, le_rfl, Nat.zero_le _, ?_⟩
    simpa only [Finset.Ico_self] using Finset.not_nonempty_iff_eq_empty.mp hs

/-- Cancellation on every interval transfers to one interval cut out by a
monotone increment sequence, without paying an extra term count. -/
theorem norm_sum_monotone_block_le {α : Type*} [LinearOrder α]
    (d : ℕ → α) (hd : Monotone d) (N : ℕ) (L R : α)
    (z : ℕ → ℂ) (C : ℝ)
    (hcancel : ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, L ≤ d j ∧ d j ≤ R) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ (Finset.range N).filter (fun j => L ≤ d j ∧ d j ≤ R), z j‖ ≤ C := by
  classical
  obtain ⟨a, b, hab, hbN, heq⟩ := monotone_filter_range_eq_Ico d hd N L R
  rw [heq]
  apply hcancel a b hab hbN
  intro j hj
  rw [← heq] at hj
  exact (Finset.mem_filter.mp hj).2

lemma phaseGoodBlock_pairwise_disjoint (d : ℕ → ℝ) (N : ℕ)
    (β : ℝ) (hβ : 0 < β) : Pairwise (fun k l : ℤ =>
      Disjoint (phaseGoodBlock d N β k) (phaseGoodBlock d N β l)) := by
  classical
  intro k l hkl
  apply Finset.disjoint_left.mpr
  intro j hjk hjl
  have hk := (Finset.mem_filter.mp hjk).2
  have hl := (Finset.mem_filter.mp hjl).2
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hgap : (k : ℝ) + 1 ≤ (l : ℝ) := by
      exact_mod_cast (show k + 1 ≤ l by omega)
    linarith
  · have hgap : (l : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (show l + 1 ≤ k by omega)
    linarith

/-- Partition a sum into good monotone derivative blocks and exceptional
indices. Each good integer cell pays just one cancellation bound. -/
theorem norm_sum_le_bad_card_add_good_blocks
    (d : ℕ → ℝ) (hd : Monotone d) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (K : Finset ℤ) (z : ℕ → ℂ) (C : ℝ)
    (hz : ∀ j < N, ‖z j‖ ≤ 1)
    (hcancel : ∀ k ∈ K, ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, z j‖ ≤
      ((Finset.range N \ K.biUnion (phaseGoodBlock d N β)).card : ℝ) +
        (K.card : ℝ) * C := by
  classical
  let G := K.biUnion (phaseGoodBlock d N β)
  have hsub : G ⊆ Finset.range N := by
    intro j hj
    obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp hjk).1
  have hdisj : (K : Set ℤ).PairwiseDisjoint (phaseGoodBlock d N β) := by
    intro k hk l hl hkl
    exact phaseGoodBlock_pairwise_disjoint d N β hβ hkl
  have hgood : ‖∑ j ∈ G, z j‖ ≤ (K.card : ℝ) * C := by
    change ‖∑ j ∈ K.biUnion (phaseGoodBlock d N β), z j‖ ≤ _
    rw [Finset.sum_biUnion hdisj]
    calc
      _ ≤ ∑ k ∈ K, ‖∑ j ∈ phaseGoodBlock d N β k, z j‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ K, C := by
        apply Finset.sum_le_sum
        intro k hk
        exact norm_sum_monotone_block_le d hd N ((k : ℝ) + β) ((k : ℝ) + 1 - β)
          z C (hcancel k hk)
      _ = _ := by simp
  have hbad : ‖∑ j ∈ Finset.range N \ G, z j‖ ≤ ((Finset.range N \ G).card : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N \ G, ‖z j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range N \ G, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hz j (Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1)
      _ = _ := by simp
  rw [← Finset.sum_sdiff hsub]
  exact (norm_add_le _ _).trans (add_le_add hbad hgood)

/-- The number of integer cells intersecting a real interval has the usual
length-plus-two bound. -/
theorem floor_interval_card_le (L U : ℝ) (hLU : L ≤ U) :
    ((Finset.Icc ⌊L⌋ ⌊U⌋).card : ℝ) ≤ U - L + 2 := by
  have hfloor : ⌊L⌋ ≤ ⌊U⌋ := Int.floor_le_floor hLU
  have hcardZ := Int.card_Icc_of_le ⌊L⌋ ⌊U⌋ (show ⌊L⌋ ≤ ⌊U⌋ + 1 by omega)
  have hcard : ((Finset.Icc ⌊L⌋ ⌊U⌋).card : ℝ) = (⌊U⌋ : ℝ) + 1 - (⌊L⌋ : ℝ) := by
    exact_mod_cast hcardZ
  rw [hcard]
  have hU := Int.floor_le U
  have hL := Int.lt_floor_add_one L
  linarith

/-- Outside the good integer cells, an increment is close to an integer. -/
theorem phase_bad_near_integer (d : ℕ → ℝ) (N : ℕ) (β L U : ℝ)
    (hrange : ∀ j < N, L ≤ d j ∧ d j ≤ U) (j : ℕ)
    (hj : j ∈ Finset.range N \ (Finset.Icc ⌊L⌋ ⌊U⌋).biUnion (phaseGoodBlock d N β)) :
    ∃ k : ℤ, |d j - (k : ℝ)| < β := by
  classical
  have hjN : j < N := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
  have hnotmem := (Finset.mem_sdiff.mp hj).2
  let k : ℤ := ⌊d j⌋
  have hk : k ∈ Finset.Icc ⌊L⌋ ⌊U⌋ :=
    Finset.mem_Icc.mpr ⟨Int.floor_le_floor (hrange j hjN).1,
      Int.floor_le_floor (hrange j hjN).2⟩
  have hnot : ¬((k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) := by
    intro hgood
    apply hnotmem
    exact Finset.mem_biUnion.mpr ⟨k, hk,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, hgood⟩⟩
  have hklo : (k : ℝ) ≤ d j := Int.floor_le _
  have hkhi : d j < (k : ℝ) + 1 := Int.lt_floor_add_one _
  by_cases hleft : d j - (k : ℝ) < β
  · refine ⟨k, ?_⟩
    rwa [abs_of_nonneg (sub_nonneg.mpr hklo)]
  · have hleft' : β ≤ d j - (k : ℝ) := le_of_not_gt hleft
    have hright : (k : ℝ) + 1 - β < d j := by
      apply lt_of_not_ge
      intro hupper
      exact hnot ⟨by linarith, hupper⟩
    refine ⟨k + 1, ?_⟩
    simp only [Int.cast_add, Int.cast_one]
    rw [abs_of_nonpos (by linarith : d j - ((k : ℝ) + 1) ≤ 0)]
    linarith

/-- A second-derivative partition estimate, separating the packing estimate
for bad points from the cancellation estimate on good intervals. -/
theorem norm_sum_le_near_integer_bound
    (d : ℕ → ℝ) (hd : Monotone d) (N : ℕ) (β L U : ℝ) (hβ : 0 < β)
    (hLU : L ≤ U) (hrange : ∀ j < N, L ≤ d j ∧ d j ≤ U)
    (z : ℕ → ℂ) (B C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ j < N, ‖z j‖ ≤ 1)
    (hbad : ((nearIntegerIndices d N β).card : ℝ) ≤ B)
    (hcancel : ∀ k ∈ Finset.Icc ⌊L⌋ ⌊U⌋, ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, z j‖ ≤ B + (U - L + 2) * C := by
  classical
  have hsub : Finset.range N \ (Finset.Icc ⌊L⌋ ⌊U⌋).biUnion (phaseGoodBlock d N β) ⊆
      (Finset.range N).filter (fun j => ∃ k : ℤ, |d j - (k : ℝ)| < β) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1,
      phase_bad_near_integer d N β L U hrange j hj⟩
  have hcard : ((Finset.range N \ (Finset.Icc ⌊L⌋ ⌊U⌋).biUnion (phaseGoodBlock d N β)).card : ℝ) ≤
      ((nearIntegerIndices d N β).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hbad' := hcard.trans hbad
  have hmain := norm_sum_le_bad_card_add_good_blocks d hd N β hβ
    (Finset.Icc ⌊L⌋ ⌊U⌋) z C hz hcancel
  exact hmain.trans (add_le_add hbad' (mul_le_mul_of_nonneg_right (floor_interval_card_le L U hLU) hC))

/-- Local monotonicity on the sampled range suffices for the partition bound;
extend by a constant after the last sampled increment. -/
theorem norm_sum_le_near_integer_bound_local
    (d : ℕ → ℝ) (N : ℕ) (hd : MonotoneOn d (Set.Iio N))
    (β L U : ℝ) (hβ : 0 < β) (hLU : L ≤ U)
    (hrange : ∀ j < N, L ≤ d j ∧ d j ≤ U)
    (z : ℕ → ℂ) (B C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ j < N, ‖z j‖ ≤ 1)
    (hbad : ((nearIntegerIndices d N β).card : ℝ) ≤ B)
    (hcancel : ∀ k ∈ Finset.Icc ⌊L⌋ ⌊U⌋, ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, z j‖ ≤ B + (U - L + 2) * C := by
  classical
  let e : ℕ → ℝ := fun j => d (min j (N - 1))
  have heq (j : ℕ) (hj : j < N) : e j = d j := by
    dsimp [e]
    rw [min_eq_left (by omega)]
  have hem : Monotone e := by
    intro i j hij
    by_cases hN : N = 0
    · simp [e, hN]
    · apply hd
      · change min i (N - 1) < N
        have := min_le_right i (N - 1)
        omega
      · change min j (N - 1) < N
        have := min_le_right j (N - 1)
        omega
      · exact min_le_min_right _ hij
  have hindices : nearIntegerIndices e N β = nearIntegerIndices d N β := by
    ext j
    by_cases hj : j < N
    · simp only [nearIntegerIndices, Finset.mem_filter, Finset.mem_range, hj, true_and, heq j hj]
    · simp only [nearIntegerIndices, Finset.mem_filter, Finset.mem_range, hj, false_and]
  apply norm_sum_le_near_integer_bound e hem N β L U hβ hLU
    (fun j hj => by simpa only [heq j hj] using hrange j hj) z B C hC hz
  · simpa only [hindices] using hbad
  · intro k hk a b hab hbN hstrip
    apply hcancel k hk a b hab hbN
    intro j hj
    have hjN : j < N := lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 hbN
    simpa only [heq j hjN] using hstrip j hj

end Problem337

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_SecondDerivativeBudget
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337

/-- The elementary square-root optimization of bad-point counting and
first-derivative cancellation, with explicit harmless constants. -/
theorem second_derivative_partition_sqrt_budget (A T lam : ℝ)
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hlam : 0 < lam) (hlamone : lam ≤ 1) :
    (A * lam * T + 2 * Real.sqrt lam + 1) * (2 * Real.sqrt lam / lam + 1) +
      (A * lam * T + 2) * (2 / Real.sqrt lam + 1) ≤
        6 * A * T * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsq : (Real.sqrt lam)^2 = lam := Real.sq_sqrt hlam.le
  have hsone : Real.sqrt lam ≤ 1 := by
    nlinarith
  have hlams : lam ≤ Real.sqrt lam := by nlinarith
  have hat : 0 ≤ A * T := mul_nonneg hA hT
  have hprod : A * T * lam ≤ A * T * Real.sqrt lam := mul_le_mul_of_nonneg_left hlams hat
  have hratio : Real.sqrt lam / lam = 1 / Real.sqrt lam := by
    apply (div_eq_div_iff hlam.ne' hs.ne').mpr
    nlinarith
  rw [mul_div_assoc, hratio]
  have heq :
      (A * lam * T + 2 * Real.sqrt lam + 1) * (2 * (1 / Real.sqrt lam) + 1) +
        (A * lam * T + 2) * (2 / Real.sqrt lam + 1) =
      4 * A * T * Real.sqrt lam + 2 * A * T * lam +
        2 * Real.sqrt lam + 6 / Real.sqrt lam + 7 := by
    field_simp
    nlinarith [mul_nonneg hat (sq_nonneg (Real.sqrt lam))]
  convert heq.le.trans (show 4 * A * T * Real.sqrt lam + 2 * A * T * lam +
      2 * Real.sqrt lam + 6 / Real.sqrt lam + 7 ≤
      6 * A * T * Real.sqrt lam + 6 / Real.sqrt lam + 9 by nlinarith) using 1
  all_goals try with_reducible_and_instances rfl

end Problem337

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_SeparatedIntervalCount
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Classical
namespace Problem337

/-- Packing bound for integer-indexed values separated at a positive linear rate. -/
theorem separated_interval_card (s : Finset ℤ) (f : ℤ → ℝ)
    (lam u v : ℝ) (hlam : 0 < lam) (huv : u ≤ v)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → lam * ((j : ℝ) - i) ≤ f j - f i)
    (hrange : ∀ i ∈ s, u ≤ f i ∧ f i ≤ v) :
    (s.card : ℝ) ≤ (v - u) / lam + 1 := by
  classical
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have ha : a ∈ s := s.min'_mem hs
    have hb : b ∈ s := s.max'_mem hs
    have hab : a ≤ b := s.min'_le b hb
    have hsub : s ⊆ Finset.Icc a b := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨s.min'_le i hi, s.le_max' i hi⟩
    have hcard : (s.card : ℝ) ≤ (b : ℝ) - a + 1 := by
      calc
        (s.card : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        _ = (b : ℝ) - a + 1 := by
          have h := Int.card_Icc_of_le a b (by omega)
          exact_mod_cast (show ((Finset.Icc a b).card : ℤ) = b - a + 1 by omega)
    have hg := hsep a ha b hb hab
    have ha' := (hrange a ha).1
    have hb' := (hrange b hb).2
    have hdiff : (b : ℝ) - a ≤ (v - u) / lam := by
      apply (le_div_iff₀ hlam).mpr
      nlinarith
    linarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The number of separated samples near integers is controlled by the number
of integer centers and the packing bound in each short interval. -/
theorem separated_near_integer_card (s : Finset ℤ) (f : ℤ → ℝ)
    (lam β L U : ℝ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hLU : L ≤ U)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → lam * ((j : ℝ) - i) ≤ f j - f i)
    (hrange : ∀ i ∈ s, L ≤ f i ∧ f i ≤ U) :
    ((s.filter fun i => ∃ q : ℤ, |f i - q| ≤ β).card : ℝ) ≤
      (U - L + 2 * β + 1) * (2 * β / lam + 1) := by
  classical
  let centers : Finset ℤ := Finset.Icc ⌈L - β⌉ ⌊U + β⌋
  let fiber (q : ℤ) : Finset ℤ := s.filter fun i => |f i - q| ≤ β
  have hcover : (s.filter fun i => ∃ q : ℤ, |f i - q| ≤ β) ⊆ centers.biUnion fiber := by
    intro i hi
    obtain ⟨his, q, hq⟩ := Finset.mem_filter.mp hi
    have hq' := abs_le.mp hq
    have hi' := hrange i his
    apply Finset.mem_biUnion.mpr
    refine ⟨q, ?_, Finset.mem_filter.mpr ⟨his, hq⟩⟩
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      linarith
    · apply Int.le_floor.mpr
      linarith
  have hfiber (q : ℤ) : ((fiber q).card : ℝ) ≤ 2 * β / lam + 1 := by
    have h := separated_interval_card (fiber q) f lam ((q : ℝ) - β) ((q : ℝ) + β)
      hlam (by linarith)
      (fun i hi j hj hij => hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
      (fun i hi => by
        have h := abs_le.mp (Finset.mem_filter.mp hi).2
        constructor <;> linarith)
    convert h using 1 <;> first | rfl | ring
  have hcenters : (centers.card : ℝ) ≤ U - L + 2 * β + 1 := by
    have h := separated_interval_card centers (fun q => (q : ℝ)) 1 (L - β) (U + β)
      (by norm_num) (by linarith) (fun i _ j _ _ => by ring_nf; exact le_rfl)
      (fun q hq => by
        have hq' := Finset.mem_Icc.mp hq
        exact ⟨Int.ceil_le.mp hq'.1, Int.le_floor.mp hq'.2⟩)
    convert h using 1 <;> first | rfl | ring
  calc
    ((s.filter fun i => ∃ q : ℤ, |f i - q| ≤ β).card : ℝ) ≤
        ((centers.biUnion fiber).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ q ∈ centers, ((fiber q).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := centers) (t := fiber))
    _ ≤ ∑ _q ∈ centers, (2 * β / lam + 1) :=
      Finset.sum_le_sum (fun q _ => hfiber q)
    _ = (centers.card : ℝ) * (2 * β / lam + 1) := by
      simp
      ring
    _ ≤ (U - L + 2 * β + 1) * (2 * β / lam + 1) :=
      mul_le_mul_of_nonneg_right hcenters (by positivity)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_DiscreteSecondDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Natural-indexed strict-neighborhood version of the separated sample bound. -/
theorem nat_separated_near_integer_card (d : ℕ → ℝ) (N : ℕ)
    (lam β L U : ℝ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hLU : L ≤ U)
    (hsep : ∀ i < N, ∀ j < N, i ≤ j → lam * ((j : ℝ) - i) ≤ d j - d i)
    (hrange : ∀ i < N, L ≤ d i ∧ d i ≤ U) :
    ((nearIntegerIndices d N β).card : ℝ) ≤
      (U - L + 2 * β + 1) * (2 * β / lam + 1) := by
  classical
  have h := separated_near_integer_card ((Finset.range N).image Int.ofNat)
    (fun i : ℤ => d i.toNat) lam β L U hlam hβ hLU
    (by
      intro i hi j hj hij
      rcases Finset.mem_image.mp hi with ⟨ii, hii, rfl⟩
      rcases Finset.mem_image.mp hj with ⟨jj, hjj, rfl⟩
      simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast, Int.cast_natCast] using
        hsep ii (Finset.mem_range.mp hii) jj (Finset.mem_range.mp hjj)
          (Int.ofNat_le.mp (by simpa only [Int.ofNat_eq_natCast] using hij)))
    (by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨ii, hii, rfl⟩
      exact hrange ii (Finset.mem_range.mp hii))
  simp only [Finset.filter_image, Int.ofNat_eq_natCast, Int.toNat_natCast] at h
  rw [Finset.card_image_of_injective _ Int.ofNat_injective] at h
  have hsub : nearIntegerIndices d N β ⊆
      (Finset.range N).filter (fun i => ∃ q : ℤ, |d i - (q : ℝ)| ≤ β) := by
    intro i hi
    obtain ⟨hiN, q, hq⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hiN, q, hq.le⟩
  exact (show ((nearIntegerIndices d N β).card : ℝ) ≤
      (((Finset.range N).filter (fun i => ∃ q : ℤ, |d i - (q : ℝ)| ≤ β)).card : ℝ) by
    exact_mod_cast Finset.card_le_card hsub).trans h

namespace ExponentialSum

/-- A strip cancellation bound needing increment information only for the
indices being summed; the final endpoint costs at most one. -/
theorem first_derivative_Ico_bound (f : ℕ → ℝ) (a b : ℕ) (β : ℝ) (q : ℤ)
    (hab : a ≤ b) (hβ : 0 < β)
    (hlo : ∀ j ∈ Finset.Ico a b, (q : ℝ) + β ≤ f (j + 1) - f j)
    (hhi : ∀ j ∈ Finset.Ico a b, f (j + 1) - f j ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio b)) :
    ‖∑ j ∈ Finset.Ico a b, phase (f j)‖ ≤ 2 / β + 1 := by
  by_cases heq : a = b
  · subst b
    simp only [Finset.Ico_self, Finset.sum_empty, norm_zero]
    positivity
  have hab' : a < b := lt_of_le_of_ne hab heq
  let n := b - a - 1
  have hn : n + 1 = b - a := by dsimp [n]; omega
  let g : ℕ → ℝ := fun i => f (a + i)
  have hinc (i : ℕ) : g (i + 1) - g i = f (a + i + 1) - f (a + i) := by
    simp only [g, Nat.add_assoc]
  have hbound := first_derivative_sum_bound_strip g n β q hβ
    (by
      intro i hi
      rw [hinc]
      apply hlo
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    (by
      intro i hi
      rw [hinc]
      apply hhi
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    (by
      intro i hi j hj hij
      change g (i + 1) - g i ≤ g (j + 1) - g j
      rw [hinc, hinc]
      have hi' : i ≤ n := hi
      have hj' : j ≤ n := hj
      exact hmono (by change a + i < b; omega) (by change a + j < b; omega) (Nat.add_le_add_left hij a))
  rw [Finset.sum_Ico_eq_sum_range, ← hn, Finset.sum_range_succ]
  exact (norm_add_le _ _).trans (add_le_add hbound (le_of_eq (phase_norm _)))

/-- A fully discrete second-derivative estimate from monotone separated phase
increments. The only analytic input is the proved first-derivative test. -/
theorem discrete_second_derivative_partition_bound (f : ℕ → ℝ) (N : ℕ)
    (lam β L U : ℝ) (hlam : 0 < lam) (hβ : 0 < β) (hLU : L ≤ U)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i))
    (hrange : ∀ j < N, L ≤ f (j + 1) - f j ∧ f (j + 1) - f j ≤ U) :
    ‖∑ j ∈ Finset.range N, phase (f j)‖ ≤
      (U - L + 2 * β + 1) * (2 * β / lam + 1) + (U - L + 2) * (2 / β + 1) := by
  apply norm_sum_le_near_integer_bound_local (fun j => f (j + 1) - f j) N hmono β L U hβ hLU hrange
    (fun j => phase (f j)) _ (2 / β + 1) (by positivity)
  · intro j hj
    exact le_of_eq (phase_norm _)
  · exact nat_separated_near_integer_card _ N lam β L U hlam hβ.le hLU hsep hrange
  · intro q hq a b hab hbN hstrip
    exact first_derivative_Ico_bound f a b β q hab hβ
      (fun j hj => (hstrip j hj).1) (fun j hj => (hstrip j hj).2)
      (by
        intro i hi j hj hij
        exact hmono (lt_of_lt_of_le hi hbN) (lt_of_lt_of_le hj hbN) hij)

/-- The square-root form used in the reciprocal-phase differencing argument. -/
theorem discrete_second_derivative_sqrt_bound (f : ℕ → ℝ) (N : ℕ)
    (lam A L : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i))
    (hrange : ∀ j < N, L ≤ f (j + 1) - f j ∧ f (j + 1) - f j ≤ L + A * lam * N) :
    ‖∑ j ∈ Finset.range N, phase (f j)‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  have h := discrete_second_derivative_partition_bound f N lam (Real.sqrt lam) L (L + A * lam * N)
    hlam (Real.sqrt_pos.mpr hlam) (le_add_of_nonneg_right (by positivity)) hmono hsep hrange
  have hb := second_derivative_partition_sqrt_budget A (N : ℝ) lam hA (Nat.cast_nonneg _) hlam hlam1
  exact h.trans (by simpa only [add_sub_cancel_left] using hb)

end ExponentialSum
end Problem337

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_ReciprocalDerivatives
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Explicit derivatives of the reciprocal phase used in deterministic cancellation. -/
theorem reciprocal_phase_iteratedDeriv (k : ℕ) (Z x : ℝ) :
    iteratedDeriv k (fun y : ℝ => Z / y) x =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) * Z / x ^ (k + 1) := by
  simp only [div_eq_mul_inv]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  ring

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_ForwardDifference
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Set
open scoped ContDiff Topology

namespace Problem337

theorem forwardDifference_contDiffOn (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) :
    ContDiffOn ℝ ∞ (forwardDifference hs f) (Ioi 0) := by
  induction hs with
  | nil => exact hf
  | cons h hs ih =>
      have hh : 0 ≤ h := hhs h (by simp)
      have ih' := ih (fun d hd => hhs d (by simp [hd]))
      change ContDiffOn ℝ ∞ (fun x => forwardDifference hs f (x + h) - forwardDifference hs f x) (Ioi 0)
      apply ContDiffOn.sub _ ih'
      apply ih'.comp (contDiffOn_id.add contDiffOn_const)
      intro x hx
      change 0 < x + h
      change 0 < x at hx
      linarith

theorem deriv_forwardDifference (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    deriv (forwardDifference hs f) x = forwardDifference hs (deriv f) x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      have hh : 0 ≤ h := hhs h (by simp)
      have htail : ∀ d ∈ hs, 0 ≤ d := fun d hd => hhs d (by simp [hd])
      have hcont := forwardDifference_contDiffOn hs htail hf
      have hx' : 0 < x + h := by linarith
      have hdiff : DifferentiableAt ℝ (forwardDifference hs f) x :=
        (hcont.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      have hdiff' : DifferentiableAt ℝ (fun y => forwardDifference hs f (y + h)) x := by
        exact ((hcont.contDiffAt (isOpen_Ioi.mem_nhds hx')).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp x
          (differentiableAt_id.add_const h)
      change deriv (fun y => forwardDifference hs f (y + h) - forwardDifference hs f y) x = _
      rw [deriv_fun_sub hdiff' hdiff, deriv_comp_add_const]
      change deriv (forwardDifference hs f) (x + h) - deriv (forwardDifference hs f) x = _
      rw [ih htail, ih htail]
      rfl
      all_goals assumption

/-- Repeated mean value theorem for positive shifts. The witness remains in the
interval swept out by all shifts. -/
theorem forwardDifference_eq_derivative (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    ∃ ξ : ℝ, x ≤ ξ ∧ ξ ≤ x + hs.sum ∧
      forwardDifference hs f x = hs.prod * iteratedDeriv hs.length f ξ := by
  induction hs generalizing f x with
  | nil => exact ⟨x, le_rfl, by simp, by simp [forwardDifference]⟩
  | cons h hs ih =>
      have hh : 0 < h := hhs h (by simp)
      have htail : ∀ d ∈ hs, 0 < d := fun d hd => hhs d (by simp [hd])
      have hnonneg : ∀ d ∈ hs, 0 ≤ d := fun d hd => (htail d hd).le
      have hcont := forwardDifference_contDiffOn hs hnonneg hf
      have hcc : Icc x (x + h) ⊆ Ioi 0 := by intro y hy; exact hx.trans_le hy.1
      have hco : Ioo x (x + h) ⊆ Ioi 0 := Ioo_subset_Icc_self.trans hcc
      obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope (forwardDifference hs f)
        (by linarith : x < x + h) (hcont.continuousOn.mono hcc)
        ((hcont.differentiableOn (by simp)).mono hco)
      have hc0 : 0 < c := hx.trans hc.1
      rw [deriv_forwardDifference hs hnonneg hf hc0] at hderiv
      have hden : x + h - x = h := by ring
      rw [hden] at hderiv
      have hmul : forwardDifference (h :: hs) f x = h * forwardDifference hs (deriv f) c := by
        have heq := (eq_div_iff hh.ne').1 hderiv
        dsimp [forwardDifference]
        nlinarith
      have hf' : ContDiffOn ℝ ∞ (deriv f) (Ioi 0) :=
        hf.deriv_of_isOpen isOpen_Ioi (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      obtain ⟨ξ, hcξ, hξ, heq⟩ := ih htail hf' hc0
      refine ⟨ξ, hc.1.le.trans hcξ, ?_, ?_⟩
      · simp only [List.sum_cons]
        linarith [hc.2]
      · rw [hmul, heq]
        simp only [List.prod_cons, List.length_cons, iteratedDeriv_succ']
        ring

theorem iteratedDeriv_forwardDifference (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (forwardDifference hs f) x = forwardDifference hs (iteratedDeriv k f) x := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      have heq : deriv (forwardDifference hs f) =ᶠ[𝓝 x] forwardDifference hs (deriv f) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact deriv_forwardDifference hs hhs hf hy
      rw [iteratedDeriv_succ', heq.iteratedDeriv_eq k]
      rw [ih (hf.deriv_of_isOpen isOpen_Ioi (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
      rw [iteratedDeriv_succ']

private theorem smooth_iteratedDeriv_Ioi (k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) : ContDiffOn ℝ ∞ (iteratedDeriv k f) (Ioi 0) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

private theorem iteratedDeriv_order_add (r k : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv r (iteratedDeriv k f) = iteratedDeriv (r + k) f := by
  induction r with
  | zero => simp
  | succ r ih => simp only [iteratedDeriv_succ, ih, Nat.succ_add]

/-- The derivative of an iterated difference is a scaled higher derivative at an
intermediate point. This avoids a multi-dimensional integral in the phase estimate. -/
theorem iteratedDeriv_forwardDifference_eq (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    ∃ ξ : ℝ, x ≤ ξ ∧ ξ ≤ x + hs.sum ∧
      iteratedDeriv k (forwardDifference hs f) x =
        hs.prod * iteratedDeriv (hs.length + k) f ξ := by
  rw [iteratedDeriv_forwardDifference k hs (fun h hh => (hhs h hh).le) hf hx]
  obtain ⟨ξ, hxξ, hξ, heq⟩ := forwardDifference_eq_derivative hs hhs
    (smooth_iteratedDeriv_Ioi k hf) hx
  refine ⟨ξ, hxξ, hξ, ?_⟩
  simpa only [iteratedDeriv_order_add] using heq

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_PhaseExtension
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

theorem affineTailPhase_increment (f : ℕ → ℝ) (N n : ℕ) :
    affineTailPhase f N (n + 1) - affineTailPhase f N n =
      f (min n (N - 1) + 1) - f (min n (N - 1)) := by
  simp only [affineTailPhase, Finset.sum_range_succ]
  ring

theorem affineTailPhase_eq (f : ℕ → ℝ) (N : ℕ) :
    ∀ n : ℕ, n ≤ N → affineTailPhase f N n = f n := by
  intro n
  induction n with
  | zero => simp [affineTailPhase]
  | succ n ih =>
    intro hn
    have hprev := ih (by omega)
    have hmin : min n (N - 1) = n := Nat.min_eq_left (by omega)
    have hinc := affineTailPhase_increment f N n
    rw [hmin] at hinc
    linarith

theorem affineTailPhase_increment_monotone (f : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N)) :
    Monotone (fun j => affineTailPhase f N (j + 1) - affineTailPhase f N j) := by
  intro i j hij
  dsimp only
  rw [affineTailPhase_increment, affineTailPhase_increment]
  apply hmono
  · change min i (N - 1) < N
    omega
  · change min j (N - 1) < N
    omega
  · omega

theorem affineTailPhase_increment_eq (f : ℕ → ℝ) (N j : ℕ) (hj : j < N) :
    affineTailPhase f N (j + 1) - affineTailPhase f N j = f (j + 1) - f j := by
  rw [affineTailPhase_increment, Nat.min_eq_left (by omega : j ≤ N - 1)]

/-- Local interval monotonicity is enough whenever a phase-sum theorem assumes
globally monotone increments: this extension preserves every sample used. -/
theorem exists_monotone_increment_extension (f : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N)) :
    ∃ g : ℕ → ℝ, (∀ j, j ≤ N → g j = f j) ∧
      Monotone (fun j => g (j + 1) - g j) ∧
      (∀ j, j < N → g (j + 1) - g j = f (j + 1) - f j) := by
  exact ⟨affineTailPhase f N, affineTailPhase_eq f N,
    affineTailPhase_increment_monotone f N hN hmono,
    affineTailPhase_increment_eq f N⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_SecondDifference
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Set

namespace Problem337

/-- A second finite difference is a second derivative value times the squared
step. Only pointwise derivative data on the relevant closed interval is used. -/
theorem second_difference_eq_deriv (f f' f'' : ℝ → ℝ) (x h : ℝ) (hh : 0 < h)
    (hf : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f' (f'' y) y) :
    ∃ c ∈ Ioo x (x + 2 * h),
      f (x + 2 * h) - 2 * f (x + h) + f x = h ^ 2 * f'' c := by
  let g : ℝ → ℝ := fun y => f (y + h) - f y
  let g' : ℝ → ℝ := fun y => f' (y + h) - f' y
  have hg : ∀ y ∈ Icc x (x + h), HasDerivAt g (g' y) y := by
    intro y hy
    have hy1 : y ∈ Icc x (x + 2 * h) := ⟨hy.1, by linarith [hy.2]⟩
    have hy2 : y + h ∈ Icc x (x + 2 * h) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have htrans := (hf (y + h) hy2).comp_add_const y h
    exact htrans.fun_sub (hf y hy1)
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope g g' (by linarith : x < x + h)
    (fun y hy => (hg y hy).continuousAt.continuousWithinAt)
    (fun y hy => hg y ⟨hy.1.le, hy.2.le⟩)
  have hinterval : Icc c (c + h) ⊆ Icc x (x + 2 * h) := by
    intro y hy
    constructor <;> linarith [hc.1, hc.2, hy.1, hy.2]
  obtain ⟨d, hd, hdeq⟩ := exists_hasDerivAt_eq_slope f' f'' (by linarith : c < c + h)
    (fun y hy => (hf' y (hinterval hy)).continuousAt.continuousWithinAt)
    (fun y hy => hf' y (hinterval ⟨hy.1.le, hy.2.le⟩))
  refine ⟨d, ⟨by linarith [hc.1, hd.1], by linarith [hc.2, hd.2]⟩, ?_⟩
  have heq' : g (x + h) - g x = h * g' c := by
    have : x + h - x = h := by ring
    rw [this] at heq
    exact (eq_div_iff (ne_of_gt hh)).mp heq |> (fun H => by nlinarith [H])
  have hdeq' : f' (c + h) - f' c = h * f'' d := by
    have : c + h - c = h := by ring
    rw [this] at hdeq
    have := (eq_div_iff (ne_of_gt hh)).mp hdeq
    nlinarith
  dsimp [g, g'] at heq'
  have hx : x + h + h = x + 2 * h := by ring
  rw [hx, hdeq'] at heq'
  nlinarith

/-- Bounds for the second derivative give bounds for each second difference. -/
theorem second_difference_bounds (f f' f'' : ℝ → ℝ) (x h L U : ℝ) (hh : 0 < h)
    (hf : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Icc x (x + 2 * h), L ≤ f'' y ∧ f'' y ≤ U) :
    h ^ 2 * L ≤ f (x + 2 * h) - 2 * f (x + h) + f x ∧
      f (x + 2 * h) - 2 * f (x + h) + f x ≤ h ^ 2 * U := by
  obtain ⟨c, hc, heq⟩ := second_difference_eq_deriv f f' f'' x h hh hf hf'
  rw [heq]
  have hb := hbound c ⟨hc.1.le, hc.2.le⟩
  exact ⟨mul_le_mul_of_nonneg_left hb.1 (sq_nonneg h),
    mul_le_mul_of_nonneg_left hb.2 (sq_nonneg h)⟩

/-- Telescoping a two-sided bound for adjacent increments. -/
theorem discrete_increment_bounds (d : ℕ → ℝ) (a b : ℕ) (L U : ℝ)
    (hab : a ≤ b)
    (hstep : ∀ j ∈ Finset.Ico a b, L ≤ d (j + 1) - d j ∧ d (j + 1) - d j ≤ U) :
    L * ((b : ℝ) - a) ≤ d b - d a ∧ d b - d a ≤ U * ((b : ℝ) - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hprev : ∀ j ∈ Finset.Ico a b, L ≤ d (j + 1) - d j ∧ d (j + 1) - d j ≤ U := by
      intro j hj
      exact hstep j (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
        (Finset.mem_Ico.mp hj).2.trans (Nat.lt_succ_self b)⟩)
    have hlast := hstep b (Finset.mem_Ico.mpr ⟨hab, by omega⟩)
    have hprior := ih hprev
    push_cast
    constructor <;> nlinarith [hprior.1, hprior.2, hlast.1, hlast.2]

/-- Continuous second-derivative bounds imply the separation hypotheses for
sampled first differences used by the discrete second-derivative test. -/
theorem sampled_increment_bounds (f f' f'' : ℝ → ℝ) (a b : ℕ) (L U : ℝ)
    (hab : a ≤ b)
    (hf : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), L ≤ f'' y ∧ f'' y ≤ U) :
    L * ((b : ℝ) - a) ≤
        (f ((b : ℝ) + 1) - f b) - (f ((a : ℝ) + 1) - f a) ∧
      (f ((b : ℝ) + 1) - f b) - (f ((a : ℝ) + 1) - f a) ≤ U * ((b : ℝ) - a) := by
  apply discrete_increment_bounds (fun n => f ((n : ℝ) + 1) - f n) a b L U hab
  intro n hn
  have hna : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
  have hnb : (n : ℝ) + 1 ≤ b := by exact_mod_cast (Finset.mem_Ico.mp hn).2
  have hsub : Icc (n : ℝ) ((n : ℝ) + 2 * 1) ⊆ Icc (a : ℝ) ((b : ℝ) + 1) := by
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  have hh := second_difference_bounds f f' f'' (n : ℝ) 1 L U (by norm_num)
    (fun y hy => hf y (hsub hy)) (fun y hy => hf' y (hsub hy))
    (fun y hy => hbound y (hsub hy))
  norm_num only [one_pow, one_mul, mul_one] at hh
  push_cast
  have heq : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
  rw [heq]
  constructor <;> linarith [hh.1, hh.2]

/-- Darboux's theorem makes the sign of a nonvanishing second derivative
constant. Absolute derivative bounds therefore give one uniform signed strip. -/
theorem second_derivative_signed_bounds (f' f'' : ℝ → ℝ) (s : Set ℝ)
    (hs : Convex ℝ s) (L U : ℝ) (hL : 0 < L)
    (hf' : ∀ x ∈ s, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ s, L ≤ |f'' x| ∧ |f'' x| ≤ U) :
    (∀ x ∈ s, L ≤ f'' x ∧ f'' x ≤ U) ∨
      (∀ x ∈ s, -U ≤ f'' x ∧ f'' x ≤ -L) := by
  have hn : ∀ x ∈ s, f'' x ≠ 0 := by
    intro x hx heq
    have := (hbound x hx).1
    rw [heq, abs_zero] at this
    linarith
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne hs
      (fun x hx => (hf' x hx).hasDerivWithinAt) hn with hneg | hpos
  · right
    intro x hx
    have hb := hbound x hx
    rw [abs_of_neg (hneg x hx)] at hb
    constructor <;> linarith [hb.1, hb.2]
  · left
    intro x hx
    simpa only [abs_of_pos (hpos x hx)] using hbound x hx

end Problem337

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_SecondDerivativeTest
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.ExponentialSum

/-- The discrete test needs monotonicity only at the sampled increments. -/
theorem discrete_second_derivative_sqrt_bound_local (f : ℕ → ℝ) (N : ℕ)
    (lam A L : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i))
    (hrange : ∀ j < N, L ≤ f (j + 1) - f j ∧
      f (j + 1) - f j ≤ L + A * lam * N) :
    ‖∑ j ∈ Finset.range N, phase (f j)‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.cast_zero, mul_zero,
      zero_mul, zero_add]
    positivity
  obtain ⟨g, hgf, hgm, hgd⟩ := exists_monotone_increment_extension f N
    (Nat.pos_of_ne_zero hN) hmono
  have h := discrete_second_derivative_sqrt_bound g N lam A L hlam hlam1 hA (hgm.monotoneOn _)
    (by
      intro i hi j hj hij
      rw [hgd i hi, hgd j hj]
      exact hsep i hi j hj hij)
    (by
      intro j hj
      rw [hgd j hj]
      exact hrange j hj)
  have heq : (∑ j ∈ Finset.range N, phase (g j)) =
      ∑ j ∈ Finset.range N, phase (f j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hgf j (Finset.mem_range.mp hj).le]
  rwa [heq] at h

/-- Sampled differences on a translated real interval. The closed support ends
at the last needed phase value, not one integer beyond it. -/
theorem translated_sampled_increment_bounds (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N i j : ℕ) (L U : ℝ) (_hi : i < N) (hj : j < N) (hij : i ≤ j)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), L ≤ f'' y ∧ f'' y ≤ U) :
    L * ((j : ℝ) - i) ≤
        (f (((j + 1 : ℕ) : ℝ) + x) - f ((j : ℝ) + x)) -
        (f (((i + 1 : ℕ) : ℝ) + x) - f ((i : ℝ) + x)) ∧
      (f (((j + 1 : ℕ) : ℝ) + x) - f ((j : ℝ) + x)) -
        (f (((i + 1 : ℕ) : ℝ) + x) - f ((i : ℝ) + x)) ≤ U * ((j : ℝ) - i) := by
  have hsupport (y : ℝ) (hy : y ∈ Set.Icc (i : ℝ) ((j : ℝ) + 1)) :
      y + x ∈ Set.Icc x (x + N) := by
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    constructor <;> linarith [hy.1, hy.2]
  have h := sampled_increment_bounds
    (fun y => f (y + x)) (fun y => f' (y + x)) (fun y => f'' (y + x))
    i j L U hij
    (fun y hy => (hf (y + x) (hsupport y hy)).comp_add_const y x)
    (fun y hy => (hf' (y + x) (hsupport y hy)).comp_add_const y x)
    (fun y hy => hbound (y + x) (hsupport y hy))
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The second-derivative test for a positive second derivative on precisely
the closed interval supporting the finite sum. -/
theorem second_derivative_sqrt_bound_positive (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N : ℕ) (lam A : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), lam ≤ f'' y ∧ f'' y ≤ A * lam) :
    ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.cast_zero, mul_zero,
      zero_mul, zero_add]
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let g : ℕ → ℝ := fun j => f ((j : ℝ) + x)
  have hb (i : ℕ) (hi : i < N) (j : ℕ) (hj : j < N) (hij : i ≤ j) :=
    translated_sampled_increment_bounds f f' f'' x N i j lam (A * lam)
      hi hj hij hf hf' hbound
  apply discrete_second_derivative_sqrt_bound_local g N lam A (g 1 - g 0)
    hlam hlam1 hA
  · intro i hi j hj hij
    have hh := (hb i hi j hj hij).1
    have hd : (0 : ℝ) ≤ (j : ℝ) - i := sub_nonneg.mpr (by exact_mod_cast hij)
    have hp : 0 ≤ lam * ((j : ℝ) - i) := mul_nonneg hlam.le hd
    dsimp [g]
    linarith
  · intro i hi j hj hij
    exact (hb i hi j hj hij).1
  · intro j hj
    have hh := hb 0 hNpos j hj (Nat.zero_le j)
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj.le
    have hp : 0 ≤ A * lam := mul_nonneg hA hlam.le
    have ht := mul_le_mul_of_nonneg_left hjN hp
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    have hl := mul_nonneg hlam.le hj0
    dsimp [g]
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_add] at hh ⊢
    constructor <;> linarith [hh.1, hh.2]

/-- The usual absolute second-derivative test. Darboux gives a uniform sign;
negative phases are handled by complex conjugation. -/
theorem second_derivative_sqrt_bound (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N : ℕ) (lam A : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), lam ≤ |f'' y| ∧ |f'' y| ≤ A * lam) :
    ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  rcases second_derivative_signed_bounds f' f'' _ (convex_Icc _ _) lam (A * lam)
      hlam hf' hbound with hpos | hneg
  · exact second_derivative_sqrt_bound_positive f f' f'' x N lam A
      hlam hlam1 hA hf hf' hpos
  · have h := second_derivative_sqrt_bound_positive
      (fun y => -f y) (fun y => -f' y) (fun y => -f'' y) x N lam A
      hlam hlam1 hA
      (fun y hy => (hf y hy).neg) (fun y hy => (hf' y hy).neg)
      (by
        intro y hy
        have hh := hneg y hy
        constructor <;> linarith [hh.1, hh.2])
    simpa only [phase_neg, ← map_sum, Complex.norm_conj] using h

/-- A uniform second-derivative estimate for every positive scale, without a
smallness hypothesis on that scale or an additive endpoint error. -/
theorem second_derivative_test (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N : ℕ) (lam A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), lam ≤ |f'' y| ∧ |f'' y| ≤ A * lam) :
    ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤
      (6 * A + 15) * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hNs : 0 ≤ (N : ℝ) * Real.sqrt lam := mul_nonneg (Nat.cast_nonneg _) hs.le
  have hinv : 0 ≤ 1 / Real.sqrt lam := by positivity
  by_cases hl1 : lam ≤ 1
  · have h := second_derivative_sqrt_bound f f' f'' x N lam A hlam hl1 hA hf hf' hbound
    have hs1 : Real.sqrt lam ≤ 1 := by nlinarith [Real.sq_sqrt hlam.le]
    have hi1 : 1 ≤ 1 / Real.sqrt lam := (le_div_iff₀ hs).2 (by simpa using hs1)
    have ha := mul_nonneg hA hinv
    apply h.trans
    have heq : 6 * A * N * Real.sqrt lam = 6 * A * ((N : ℝ) * Real.sqrt lam) := by ring
    rw [heq]
    simp only [div_eq_mul_inv, one_mul] at hi1 ha ⊢
    nlinarith
  · have hs1 : 1 ≤ Real.sqrt lam := by nlinarith [Real.sq_sqrt hlam.le]
    have hnorm : ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤ (N : ℝ) := by
      calc
        _ ≤ ∑ j ∈ Finset.range N, ‖phase (f ((j : ℝ) + x))‖ := norm_sum_le _ _
        _ = (N : ℝ) := by simp only [phase_norm, Finset.sum_const, Finset.card_range,
                            nsmul_eq_mul, mul_one]
    apply hnorm.trans
    have hN := mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have ha := mul_nonneg hA (add_nonneg hNs hinv)
    nlinarith

end Problem337.ExponentialSum

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ChebyshevDischarge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Chebyshev estimate needed for finite prime-product errors -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem primeCounting_le_self (N : ℕ) : Nat.primeCounting N ≤ N := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    _ ≤ (Icc 1 N).card := card_le_card (fun p hp =>
      mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.one_le,(Nat.mem_primesLE.mp hp).1⟩)
    _ = N := by simp

theorem chebyshevPrimeCountingInput : PublishedInputs.ChebyshevPrimeCountingInput := by
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  let C : ℝ := max (Real.log 4+1) (Real.log (max 2 x₀))
  have hC : 0 ≤ C := (by positivity : (0 : ℝ) ≤ Real.log 4+1).trans (le_max_left _ _)
  refine ⟨C,hC,fun x hx => ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hxx : x₀ ≤ x
  · exact (hx₀ x hxx).trans (by
      apply div_le_div_of_nonneg_right _ hlog.le
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · have hpn : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast primeCounting_le_self ⌊x⌋₊
    have hp : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x :=
      hpn.trans (Nat.floor_le (by linarith))
    have hlC : Real.log x ≤ C :=
      (Real.log_le_log (by linarith) ((le_of_not_ge hxx).trans (le_max_right _ _))).trans
        (le_max_right _ _)
    apply (le_div_iff₀ hlog).mpr
    calc
      _ ≤ x * Real.log x := mul_le_mul_of_nonneg_right hp hlog.le
      _ ≤ x * C := mul_le_mul_of_nonneg_left hlC (by linarith)
      _ = _ := mul_comm _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquare
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Dirichlet-polynomial mean squares, using the integrable
exponential majorant and its exact quadratic-decay Fourier transform. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset Set
open scoped BigOperators ComplexConjugate

lemma mrt_phase_pair (x y : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) *
        conj (Complex.exp ((y : ℂ) * Complex.I)) =
      Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I, ofReal_sub]
  ring

/-- A symmetric positive kernel is bounded on the squared norm by its
largest row sum.  The numerical row estimate is proved separately. -/
lemma mrt_symmetric_row_bound {ι : Type*} (S : Finset ι) (K : ι → ι → ℝ)
    (v : ι → ℝ) (C : ℝ) (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, v i * v j * K i j) ≤ C * ∑ i ∈ S, (v i) ^ 2 := by
  have he : (∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j) =
      ∑ i ∈ S, (v i) ^ 2 * ∑ j ∈ S, K i j := by
    simp only [add_div, add_mul, sum_add_distrib]
    rw [sum_comm (s := S) (t := S) (f := fun i j => (v j) ^ 2 / 2 * K i j)]
    simp only [← mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hk : (∑ j ∈ S, K j i) = ∑ j ∈ S, K i j :=
      sum_congr rfl fun j hj => hsymm j hj i hi
    rw [hk]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hK i hi j hj)
      nlinarith [sq_nonneg (v i - v j)]
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * C := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

lemma mrtExponentialPolynomial_continuous {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) : Continuous (mrtExponentialPolynomial S a freq) := by
  unfold mrtExponentialPolynomial
  fun_prop

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMultiplicativeReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := ite_eq_right hn.ne'

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCofactorWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cofactor polynomial has an actual fixed multiplicative window.
Finite partial summation turns its ordinary reciprocal-count prefix bound
into a pointwise bound for that polynomial. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

lemma mrt_cofactor_window_set (N : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    ((Icc 1 (4 * N)).filter (fun m : ℕ => (N : ℝ) < a * (m : ℝ) ∧ a * (m : ℝ) ≤ 2 * N)) =
      Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊ := by
  have ha0 : 0 < a := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hfloor : ⌊(2 * N : ℝ) / a⌋₊ ≤ 4 * N := by
    apply Nat.floor_le_of_le
    have hdiv : (2 * N : ℝ) / a ≤ 2 * N := div_le_self (by positivity) ha
    push_cast
    linarith
  ext m
  constructor
  · intro hm
    obtain ⟨hm, hlo, hhi⟩ := mem_filter.mp hm
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (div_nonneg hN0 ha0.le)).mpr
      apply (div_lt_iff₀ ha0).mpr
      simpa only [mul_comm] using hlo
    · apply Nat.le_floor
      apply (le_div_iff₀ ha0).mpr
      simpa only [mul_comm] using hhi
  · intro hm
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hm
    have hloR := (Nat.floor_lt (div_nonneg hN0 ha0.le)).mp hlo
    have hhiR : (m : ℝ) ≤ (2 * N : ℝ) / a :=
      (Nat.le_floor_iff (by positivity)).mp hhi
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by omega, hhi.trans hfloor⟩, ?_⟩
    constructor
    · simpa only [mul_comm] using (div_lt_iff₀ ha0).mp hloR
    · simpa only [mul_comm] using (le_div_iff₀ ha0).mp hhiR

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCofactorMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A mean-square bound for the actual fixed-window cofactor polynomial.
The reciprocal-count weight is a contraction, so this estimate is uniform
in all remaining typical-factorization masks. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_cofactor_exponential_polynomial (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) {a : ℝ} (ha : 1 ≤ a) (t : ℝ) :
    mrtCofactorPolynomial P F N a t =
      mrtExponentialPolynomial (Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊)
        (fun n => (F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtCofactorPolynomial
  rw [← sum_filter, mrt_cofactor_window_set N ha]
  unfold mrtExponentialPolynomial
  apply sum_congr rfl
  intro n _
  unfold mrtDirichletAtom
  ring

lemma mrt_reciprocal_count_oneBounded (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) :
    OneBounded (fun n => F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) := by
  intro n hn
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_one (by positivity : (0 : ℝ) < (finitePrimeDivisorCount P n + 1 : ℕ))).mpr
  exact (hF n hn).trans (by norm_num)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTGeneralTypical
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual typical-set Ramaré approximation for ordinary
multiplicative functions. Prime squares account for every failure of
complete multiplicativity, before any frequency-class witness cover. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrtCofactorPolynomial_continuous (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) (a : ℝ) : Continuous (mrtCofactorPolynomial P F N a) := by
  unfold mrtCofactorPolynomial
  apply continuous_finsetSum
  intro m _
  by_cases hw : (N : ℝ) < a * m ∧ a * m ≤ 2 * N
  · simp only [ite_eq_left hw]
    unfold mrtDirichletAtom
    fun_prop
  · simp only [ite_eq_right hw]
    exact continuous_const

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SeparatedCellIntegral
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering an integral from separated samples in unit-sized cells -/
namespace JointDickman
open Finset MeasureTheory
open scoped Classical

lemma unit_measure_integral_sample {E : Set ℝ} (F : ℝ → ℝ)
    (hF : IntegrableOn F E) (hF0 : ∀ x ∈ E, 0 ≤ F x)
    (hE : volume E ≠ 0) (hEf : volume E ≠ ⊤) (hE1 : volume.real E ≤ 1) :
    ∃ x ∈ E, (∫ t in E, F t) ≤ F x := by
  obtain ⟨x,hx,havg⟩ := exists_setAverage_le hE hEf hF
  have hr : 0 < volume.real E := ENNReal.toReal_pos hE hEf
  rw [setAverage_eq,smul_eq_mul,← div_eq_inv_mul] at havg
  exact ⟨x,hx,((div_le_iff₀ hr).mp havg).trans
    (mul_le_of_le_one_right (hF0 x hx) hE1)⟩

/-- Each cell has measure at most one and cells in the family are separated.
The sample bound is therefore also a bound for the sum of their integrals. -/
theorem separated_cell_integral_bound (I : Finset ℕ) (E : ℕ → Set ℝ)
    (S : Set ℝ) (F : ℝ → ℝ) (B : ℝ)
    (hF : ∀ i ∈ I, IntegrableOn F (E i)) (hF0 : ∀ x ∈ S, 0 ≤ F x)
    (hES : ∀ i ∈ I, E i ⊆ S)
    (hEf : ∀ i ∈ I, volume (E i) ≠ ⊤)
    (hE1 : ∀ i ∈ I, volume.real (E i) ≤ 1)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ x ∈ E i, ∀ y ∈ E j, 1 ≤ |x-y|)
    (hsample : ∀ U : Finset ℝ, (∀ x ∈ U, x ∈ S) →
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) → (∑ x ∈ U, F x) ≤ B) :
    (∑ i ∈ I, ∫ t in E i, F t) ≤ B := by
  let J := I.filter (fun i => volume (E i) ≠ 0)
  have hex : ∀ i ∈ J, ∃ x ∈ E i, (∫ t in E i, F t) ≤ F x := by
    intro i hi
    obtain ⟨hi,hz⟩ := mem_filter.mp hi
    exact unit_measure_integral_sample F (hF i hi) (fun x hx => hF0 x (hES i hi hx))
      hz (hEf i hi) (hE1 i hi)
  let pick : ℕ → ℝ := fun i => if hi : i ∈ J then (hex i hi).choose else 0
  have hpick : ∀ i ∈ J, pick i ∈ E i ∧ (∫ t in E i, F t) ≤ F (pick i) := by
    intro i hi
    dsimp only [pick]
    rw [dite_eq_left hi]
    exact (hex i hi).choose_spec
  have hinj : Set.InjOn pick J := by
    intro i hi j hj hij
    by_contra hne
    have hh := hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hne
      (pick i) (hpick i hi).1 (pick j) (hpick j hj).1
    rw [hij,sub_self,abs_zero] at hh
    norm_num at hh
  have hsum : (∑ i ∈ I, ∫ t in E i, F t) = ∑ i ∈ J, ∫ t in E i, F t := by
    symm
    apply sum_subset (filter_subset _ _)
    intro i hi hij
    have hz : volume (E i) = 0 := by
      by_contra hz
      exact hij (mem_filter.mpr ⟨hi,hz⟩)
    rw [Measure.restrict_eq_zero.mpr hz]
    simp
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ J, F (pick i) := sum_le_sum (fun i hi => (hpick i hi).2)
    _ = ∑ x ∈ J.image pick, F x := (sum_image hinj).symm
    _ ≤ B := hsample _ (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact hES i (mem_filter.mp hi).1 (hpick i hi).1) (by
      intro x hx y hy hxy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
      exact hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1
        (fun hij => hxy (congrArg pick hij)) (pick i) (hpick i hi).1 (pick j) (hpick j hj).1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IntegralFromSamples
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integral bound from all separated finite frequency samples -/
namespace JointDickman
open Finset MeasureTheory Function
open scoped Classical

lemma unit_grid_cover {a : ℝ} {M : ℕ} {S : Set ℝ}
    (hS : S ⊆ Set.Ico a (a+M)) :
    S = ⋃ j ∈ range M, S ∩ Set.Ico (a+j) (a+(j+1:ℕ)) := by
  ext t
  constructor
  · intro ht
    have hs := hS ht
    let j := ⌊t-a⌋₊
    have hta : 0 ≤ t-a := by linarith [hs.1]
    have hj : j < M := (Nat.floor_lt hta).mpr (by linarith [hs.2])
    have hlo := Nat.floor_le hta
    have hhi := Nat.lt_floor_add_one (t-a)
    refine Set.mem_iUnion₂.mpr ⟨j,mem_range.mpr hj,ht,?_,?_⟩
    · dsimp [j]
      linarith
    · change t < a+(j+1:ℕ)
      push_cast
      dsimp [j]
      linarith
  · intro ht
    obtain ⟨j,_,ht⟩ := Set.mem_iUnion₂.mp ht
    exact ht.1

lemma unit_grid_same_parity_separated (a : ℝ) {i j : ℕ}
    (hp : i%2=j%2) (hne : i≠j) {x y : ℝ}
    (hx : x ∈ Set.Ico (a+i) (a+(i+1:ℕ)))
    (hy : y ∈ Set.Ico (a+j) (a+(j+1:ℕ))) : 1 ≤ |x-y| := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hgap : i+2 ≤ j := by omega
    have hgr : (i:ℝ)+2 ≤ j := by exact_mod_cast hgap
    have hxi : x < a+(i:ℝ)+1 := by simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hx.2
    have hyl : a+(j:ℝ) ≤ y := hy.1
    have hh : 1 ≤ y-x := by linarith
    exact hh.trans (by simpa only [abs_sub_comm] using le_abs_self (y-x))
  · have hgap : j+2 ≤ i := by omega
    have hgr : (j:ℝ)+2 ≤ i := by exact_mod_cast hgap
    have hyj : y < a+(j:ℝ)+1 := by simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hy.2
    have hxl : a+(i:ℝ) ≤ x := hx.1
    exact (show 1 ≤ x-y by linarith).trans (le_abs_self _)

/-- A unit grid splits into two separated classes. No regularity of the
frequency set beyond measurability is required. -/
theorem integral_le_twice_separated_samples (S : Set ℝ) (hSm : MeasurableSet S)
    (F : ℝ → ℝ) (hF0 : ∀ x ∈ S, 0 ≤ F x) (a : ℝ) (M : ℕ)
    (hS : S ⊆ Set.Ico a (a+M)) (hF : IntegrableOn F (Set.Ico a (a+M))) (B : ℝ)
    (hsample : ∀ U : Finset ℝ, (∀ x ∈ U, x ∈ S) →
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) → (∑ x ∈ U, F x) ≤ B) :
    (∫ x in S, F x) ≤ 2*B := by
  let E := fun j : ℕ => S ∩ Set.Ico (a+j) (a+(j+1:ℕ))
  have hEi : ∀ j ∈ range M, IntegrableOn F (E j) :=
    fun j _ => hF.mono_set (fun x hx => hS hx.1)
  have hEm : ∀ j ∈ range M, MeasurableSet (E j) := fun _ _ => hSm.inter measurableSet_Ico
  have hEf : ∀ j ∈ range M, volume (E j) ≠ ⊤ := by
    intro j _
    exact ne_top_of_le_ne_top (measure_Ico_lt_top (μ := volume)).ne
      (measure_mono Set.inter_subset_right)
  have hE1 : ∀ j ∈ range M, volume.real (E j) ≤ 1 := by
    intro j _
    have hh := measureReal_mono (μ := volume)
      (show E j ⊆ Set.Ico (a+j) (a+(j+1:ℕ)) from Set.inter_subset_right)
      (measure_Ico_lt_top (μ := volume)).ne
    rw [Real.volume_real_Ico] at hh
    have he : a+((j+1:ℕ):ℝ)-(a+(j:ℝ))=1 := by push_cast <;> ring
    simpa only [he,max_eq_left (by norm_num : (0:ℝ)≤1)] using hh
  have hdis : Set.Pairwise (↑(range M)) (Disjoint on E) := by
    intro i hi j hj hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hxL := hx.2.1
    have hxU := hx.2.2
    have hyL := hy.2.1
    have hyU := hy.2.2
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hh : (i:ℝ)+1 ≤ j := by exact_mod_cast hij
      push_cast at hxU
      linarith
    · have hh : (j:ℝ)+1 ≤ i := by exact_mod_cast hji
      push_cast at hyU
      linarith
  have hI : (∫ x in S, F x) = ∑ j ∈ range M, ∫ x in E j, F x := by
    calc
      _ = ∫ x in ⋃ j ∈ range M, E j, F x := by
        rw [← unit_grid_cover hS]
      _ = _ := integral_biUnion_finset (range M) hEm hdis hEi
  let I₀ := (range M).filter (fun j => j%2=0)
  let I₁ := (range M).filter (fun j => ¬j%2=0)
  have hclass (I : Finset ℕ) (hI : I ⊆ range M)
      (hp : ∀ i ∈ I, ∀ j ∈ I, i%2=j%2) : (∑ j ∈ I, ∫ x in E j, F x) ≤ B := by
    apply separated_cell_integral_bound I E S F B (fun j hj => hEi j (hI hj)) hF0
      (fun _ _ => Set.inter_subset_left) (fun j hj => hEf j (hI hj))
      (fun j hj => hE1 j (hI hj)) _ hsample
    intro i hi j hj hne x hx y hy
    exact unit_grid_same_parity_separated a (hp i hi j hj) hne hx.2 hy.2
  have h₀ := hclass I₀ (filter_subset _ _) (by
    intro i hi j hj
    exact (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  have h₁ := hclass I₁ (filter_subset _ _) (by
    intro i hi j hj
    have hi := (mem_filter.mp hi).2
    have hj := (mem_filter.mp hj).2
    omega)
  rw [hI,← sum_filter_add_sum_filter_not (range M) (fun j => j%2=0)]
  change (∑ j ∈ I₀, ∫ x in E j, F x)+(∑ j ∈ I₁, ∫ x in E j, F x) ≤ 2*B
  linarith

/-- The bounded-frequency form used for Mellin polynomials. -/
theorem bounded_integral_le_twice_samples (S : Set ℝ) (hSm : MeasurableSet S)
    (F : ℝ → ℝ) (hF : Continuous F) (hF0 : ∀ x ∈ S, 0 ≤ F x)
    {T : ℝ} (_hT : 0 ≤ T) (hS : S ⊆ Set.Ioc (-T) T) (B : ℝ)
    (hsample : ∀ U : Finset ℝ, (∀ x ∈ U, x ∈ S) →
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) → (∑ x ∈ U, F x) ≤ B) :
    (∫ x in S, F x) ≤ 2*B := by
  let a := -T-1
  let M := ⌈2*T+2⌉₊
  have hcover : S ⊆ Set.Ico a (a+M) := by
    intro x hx
    obtain ⟨hslo,hshi⟩ := hS hx
    have hc := Nat.le_ceil (2*T+2)
    dsimp [a,M]
    constructor <;> linarith
  exact integral_le_twice_separated_samples S hSm F hF0 a M hcover
    (hF.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self) B hsample

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSampleDuality
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite duality for sampled Mellin polynomials

Finite duality reduces sparse-prime sampling to a row bound for the
weighted Mellin kernel.
-/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped ComplexConjugate

lemma norm_finite_complex_pairing_sq {ι : Type*} (S : Finset ι) (a b : ι → ℂ) :
    ‖∑ n ∈ S, a n*b n‖^2 ≤
      (∑ n ∈ S, ‖a n‖^2)*(∑ n ∈ S, ‖b n‖^2) := by
  have h := norm_sum_le S (fun n => a n*b n)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (sum_mul_sq_le_sq_mul_sq S (fun n => ‖a n‖) (fun n => ‖b n‖))

/-- Finite transpose duality, with no compactness or limiting argument. -/
theorem mellin_samples_of_dual (P : Finset ℕ) (S : Finset ℝ)
    (a : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hdual : ∀ b : ℝ → ℂ,
      (∑ n ∈ P, ‖∑ t ∈ S, b t *
        Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2) ≤
          C*∑ t ∈ S, ‖b t‖^2) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun n => -Real.log (n : ℝ)) t‖^2) ≤
      C*∑ n ∈ P, ‖a n‖^2 := by
  let q := mrtExponentialPolynomial P a (fun n => -Real.log (n : ℝ))
  let d : ℕ → ℂ := fun n => ∑ t ∈ S, conj (q t)*
    Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)
  let E : ℝ := ∑ t ∈ S, ‖q t‖^2
  let F : ℝ := ∑ n ∈ P, ‖a n‖^2
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  have hF : 0 ≤ F := sum_nonneg fun _ _ => sq_nonneg _
  have hpair : (∑ n ∈ P, a n*d n) = (E : ℂ) := by
    dsimp only [d, E]
    simp only [mul_sum, Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.mul_conj']
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    dsimp only [q, mrtExponentialPolynomial]
    rw [sum_mul]
    apply sum_congr rfl
    intro n _
    ring
  have hD : (∑ n ∈ P, ‖d n‖^2) ≤ C*E := by
    simpa only [d, E, Complex.norm_conj] using hdual (fun t => conj (q t))
  have hsq := norm_finite_complex_pairing_sq P a d
  rw [hpair, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hsq
  change E^2 ≤ F*∑ n ∈ P, ‖d n‖^2 at hsq
  have hh := hsq.trans (mul_le_mul_of_nonneg_left hD hF)
  change E ≤ C*F
  by_cases hz : E = 0
  · rw [hz]
    positivity
  · have hp : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
    nlinarith

lemma mellinSampleKernel_neg (P : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) :
    mellinSampleKernel P w (-t) = conj (mellinSampleKernel P w t) := by
  unfold mellinSampleKernel
  simp only [map_sum, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  apply sum_congr rfl
  intro n _
  congr 2
  simp only [Complex.conj_I, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

lemma mellin_weighted_dual_identity (P : Finset ℕ) (S : Finset ℝ)
    (w : ℕ → ℝ) (b : ℝ → ℂ) :
    (∑ n ∈ P, w n*‖∑ t ∈ S, b t *
      Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2) =
      ∑ t ∈ S, ∑ u ∈ S,
        ((b t*conj (b u))*mellinSampleKernel P w (t-u)).re := by
  have he : ((∑ n ∈ P, w n*‖∑ t ∈ S, b t *
      Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2 : ℝ) : ℂ) =
      ∑ t ∈ S, ∑ u ∈ S,
        (b t*conj (b u))*mellinSampleKernel P w (t-u) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
      ← Complex.mul_conj', map_sum, map_mul, sum_mul, mul_sum]
    rw [sum_comm]
    conv_lhs => arg 2; ext t; rw [sum_comm]
    rw [sum_comm (s := S) (t := S)]
    apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro u _
    unfold mellinSampleKernel
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    have hh := mrt_phase_pair (-Real.log (n : ℝ)*t) (-Real.log (n : ℝ)*u)
    rw [show -Real.log (n : ℝ)*t - -Real.log (n : ℝ)*u =
      -Real.log (n : ℝ)*(t-u) by ring] at hh
    rw [← hh]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, mul_assoc, mul_comm, mul_left_comm]
  simpa only [Complex.ofReal_re, Complex.re_sum] using congrArg Complex.re he

/-- A row bound for the weighted Mellin kernel controls the dual
quadratic form. -/
theorem mellin_weighted_dual_rows (P : Finset ℕ) (S : Finset ℝ)
    (w : ℕ → ℝ) {C : ℝ}
    (hrow : ∀ t ∈ S, ∑ u ∈ S, ‖mellinSampleKernel P w (t-u)‖ ≤ C)
    (b : ℝ → ℂ) :
    (∑ n ∈ P, w n*‖∑ t ∈ S, b t *
      Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2) ≤
        C*∑ t ∈ S, ‖b t‖^2 := by
  rw [mellin_weighted_dual_identity]
  apply le_trans (b := ∑ t ∈ S, ∑ u ∈ S,
    ‖b t‖*‖b u‖*‖mellinSampleKernel P w (t-u)‖)
  · apply sum_le_sum
    intro t _
    apply sum_le_sum
    intro u _
    simpa only [norm_mul, Complex.norm_conj] using Complex.re_le_norm
      ((b t*conj (b u))*mellinSampleKernel P w (t-u))
  · apply mrt_symmetric_row_bound S _ (fun t => ‖b t‖) C
      (fun _ _ _ _ => norm_nonneg _) _ hrow
    intro t _ u _
    have hh := mellinSampleKernel_neg P w (t-u)
    rw [neg_sub] at hh
    rw [hh, Complex.norm_conj]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseDerivatives
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of the logarithmic phases in character sums -/
namespace JointDickman
open Set Filter Problem337
open scoped Topology ContDiff

lemma logarithmic_phase_smooth (Z : ℝ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => Z*Real.log y) (Ioi 0) :=
  contDiffOn_const.mul (Real.contDiffOn_log.mono (fun _ hx => ne_of_gt hx))

lemma logarithmic_phase_iteratedDeriv (k : ℕ) (Z : ℝ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (k+1) (fun y : ℝ => Z*Real.log y) x =
      (-1:ℝ)^k*(k.factorial:ℝ)*Z/x^(k+1) := by
  have he : deriv (fun y : ℝ => Z*Real.log y) =ᶠ[𝓝 x] (fun y => Z/y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    have hd := (Real.hasDerivAt_log (ne_of_gt hy)).const_mul Z
    simpa only [div_eq_mul_inv] using hd.deriv
  rw [iteratedDeriv_succ',he.iteratedDeriv_eq k]
  exact reciprocal_phase_iteratedDeriv k Z x

lemma logarithmic_linear_phase_smooth (a Z : ℝ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => a*y+Z*Real.log y) (Ioi 0) :=
  (contDiffOn_const.mul contDiffOn_id).add (logarithmic_phase_smooth Z)

lemma logarithmic_linear_phase_iteratedDeriv (k : ℕ) (a Z : ℝ)
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (k+2) (fun y : ℝ => a*y+Z*Real.log y) x =
      (-1:ℝ)^(k+1)*((k+1).factorial:ℝ)*Z/x^(k+2) := by
  have hlin : ContDiffAt ℝ (k+2) (fun y : ℝ => a*y) x :=
    (contDiff_const.mul contDiff_id).contDiffAt
  have hlog : ContDiffAt ℝ (k+2) (fun y : ℝ => Z*Real.log y) x :=
    ((logarithmic_phase_smooth Z).contDiffAt (isOpen_Ioi.mem_nhds hx)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [iteratedDeriv_fun_add hlin hlog,iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_fun_id,show k+2 ≠ 0 by omega,show k+2 ≠ 1 by omega,
    ite_false, if_false,mul_zero,zero_add]
  exact logarithmic_phase_iteratedDeriv (k+1) Z hx

lemma abs_logarithmic_linear_phase_iteratedDeriv (k : ℕ) (a Z : ℝ)
    {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv (k+2) (fun y : ℝ => a*y+Z*Real.log y) x| =
      ((k+1).factorial:ℝ)*|Z|/x^(k+2) := by
  rw [logarithmic_linear_phase_iteratedDeriv k a Z hx]
  simp [abs_div,abs_mul,abs_pow,abs_of_pos hx]

lemma logarithmic_linear_forwardDifference_second_bounds (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (a Z : ℝ) {U V x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxV : x+hs.sum ≤ V) :
    hs.prod*((hs.length+1).factorial:ℝ)*|Z|/V^(hs.length+2) ≤
      |iteratedDeriv 2 (forwardDifference hs (fun y => a*y+Z*Real.log y)) x| ∧
    |iteratedDeriv 2 (forwardDifference hs (fun y => a*y+Z*Real.log y)) x| ≤
      hs.prod*((hs.length+1).factorial:ℝ)*|Z|/U^(hs.length+2) := by
  obtain ⟨ξ,hxξ,hξ,he⟩ := iteratedDeriv_forwardDifference_eq 2 hs hhs
    (logarithmic_linear_phase_smooth a Z) (hU.trans_le hx)
  have hξ0 : 0 < ξ := hU.trans_le (hx.trans hxξ)
  have hp : 0 ≤ hs.prod := List.prod_nonneg (fun h hh => (hhs h hh).le)
  rw [he,abs_mul,abs_of_nonneg hp,
    abs_logarithmic_linear_phase_iteratedDeriv hs.length a Z hξ0]
  constructor
  · have hpow := pow_le_pow_left₀ hξ0.le (hξ.trans hxV) (hs.length+2)
    have hd := div_le_div_of_nonneg_left (by positivity : 0≤((hs.length+1).factorial:ℝ)*|Z|)
      (pow_pos hξ0 _) hpow
    simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hd hp
  · have hpow := pow_le_pow_left₀ hU.le (hx.trans hxξ) (hs.length+2)
    have hd := div_le_div_of_nonneg_left (by positivity : 0≤((hs.length+1).factorial:ℝ)*|Z|)
      (pow_pos hU _) hpow
    simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hd hp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseSecondDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second-derivative bound after logarithmic differencing -/
namespace JointDickman
open Set Problem337
open scoped ContDiff

/-- All derivative information is proved for the actual logarithmic phase.
The interval includes the full displacement introduced by differencing. -/
theorem logarithmic_difference_sum_bound (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (a Z U x : ℝ) (N : ℕ)
    (hZ : Z ≠ 0) (hU : 0 < U) (hx : U ≤ x)
    (hend : x+(N:ℝ)+hs.sum ≤ 4*U) :
    let lam : ℝ := hs.prod*((hs.length+1).factorial:ℝ)*|Z|/(4*U)^(hs.length+2)
    ‖∑ j ∈ Finset.range N, ExponentialSum.phase
      (forwardDifference hs (fun y => a*y+Z*Real.log y) ((j:ℝ)+x))‖ ≤
      (6*(4:ℝ)^(hs.length+2)+15)*((N:ℝ)*Real.sqrt lam+1/Real.sqrt lam) := by
  let g : ℝ → ℝ := forwardDifference hs (fun y => a*y+Z*Real.log y)
  let lam : ℝ := hs.prod*((hs.length+1).factorial:ℝ)*|Z|/(4*U)^(hs.length+2)
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos (mul_pos (mul_pos (List.prod_pos hhs)
      (by exact_mod_cast Nat.factorial_pos _)) (abs_pos.mpr hZ)) (by positivity)
  have hg : ContDiffOn ℝ ∞ g (Ioi 0) :=
    forwardDifference_contDiffOn hs (fun h hh => (hhs h hh).le)
      (logarithmic_linear_phase_smooth a Z)
  have hg' : ContDiffOn ℝ ∞ (deriv g) (Ioi 0) :=
    hg.deriv_of_isOpen isOpen_Ioi (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hy0 (y : ℝ) (hy : y ∈ Icc x (x+N)) : 0 < y := hU.trans_le (hx.trans hy.1)
  have hf (y : ℝ) (hy : y ∈ Icc x (x+N)) : HasDerivAt g (deriv g y) y :=
    ((hg.contDiffAt (isOpen_Ioi.mem_nhds (hy0 y hy))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt
  have hf' (y : ℝ) (hy : y ∈ Icc x (x+N)) :
      HasDerivAt (deriv g) (iteratedDeriv 2 g y) y := by
    simpa only [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_zero] using
      ((hg'.contDiffAt (isOpen_Ioi.mem_nhds (hy0 y hy))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt
  have hb (y : ℝ) (hy : y ∈ Icc x (x+N)) :
      lam ≤ |iteratedDeriv 2 g y| ∧
      |iteratedDeriv 2 g y| ≤ (4:ℝ)^(hs.length+2)*lam := by
    have hh := logarithmic_linear_forwardDifference_second_bounds hs hhs a Z (V := 4*U) hU
      (hx.trans hy.1) (by linarith [hy.2])
    refine ⟨hh.1,hh.2.trans_eq ?_⟩
    dsimp [lam]
    rw [mul_pow]
    field_simp
  exact ExponentialSum.second_derivative_test g (deriv g) (iteratedDeriv 2 g)
    x N lam ((4:ℝ)^(hs.length+2)) hlam (by positivity) hf hf' hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DyadicPrimePartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dyadic partition of a finite prime set -/
namespace JointDickman
open Finset

lemma dyadic_block_count_le (N : ℕ) :
    ((Nat.log 2 N+1:ℕ):ℝ) ≤ 1+Real.log N/Real.log 2 := by
  have h := Real.natLog_le_logb N 2
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Real.logb,add_comm] using
    add_le_add h (le_refl (1:ℝ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveBudget
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary budgets for sparse prime sampling -/
namespace JointDickman
open Filter Finset
open scoped Topology

lemma prime_survival_eventually_le : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop,
      (∏ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, (1-1/(p:ℝ))) ≤ C/Real.log x := by
  let C := Real.exp (-Real.eulerMascheroniConstant)+1
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨C,hC,?_⟩
  have hh := primeProductMertensInput_jd.eventually
    (eventually_lt_nhds (lt_add_one (Real.exp (-Real.eulerMascheroniConstant))))
  filter_upwards [hh, eventually_gt_atTop (1:ℝ)] with x hx hx1
  rw [le_div_iff₀ (Real.log_pos hx1)]
  simpa only [mul_comm] using hx.le

lemma logarithmic_power_decay (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => (Real.log x)^k*x^(-a)) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (k:ℝ) ha).tendsto_div_nhds_zero
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [Real.rpow_natCast, Real.rpow_neg hx.le, div_eq_mul_inv]

lemma mellinSparseBudget_tendsto (A : ℝ) {δ κ : ℝ} (hδ : 0 < δ)
    (hκ : κ ≤ 1/8) (hκδ : κ ≤ δ) :
    Tendsto (mellinSparseBudget A δ κ) atTop (𝓝 0) := by
  have h1 : 0 < 1-2*κ := by linarith
  have h2 : 0 < 10*δ-2*κ := by linarith
  have ha := (logarithmic_power_decay 1 h1).const_mul 132
  have hb := (logarithmic_power_decay 2 h2).const_mul (176*A)
  have hh := ha.add hb
  simp only [mul_zero, add_zero] at hh
  apply hh.congr
  intro q
  dsimp [mellinSparseBudget]
  rw [show -(1-2*κ) = 2*κ-1 by ring, show -(10*δ-2*κ) = 2*κ-10*δ by ring]
  ring

lemma mellin_dyadic_count_le {q : ℕ} (hq : 2 ≤ q) :
    ((Nat.log 2 (q^3)+1:ℕ):ℝ) ≤ 8*Real.log q := by
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlog : (1/2:ℝ) ≤ Real.log q := hlog2.trans
    (Real.log_le_log (by norm_num) hqR)
  have hh := dyadic_block_count_le (q^3)
  rw [Nat.cast_pow, Real.log_pow] at hh
  have hd : Real.log ((q:ℝ)) * 3 / Real.log 2 ≤ 6*Real.log q := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith
  have hd' : 3*Real.log (q:ℝ)/Real.log 2 ≤ 6*Real.log q := by simpa only [mul_comm] using hd
  norm_num only [Nat.cast_ofNat] at hh
  linarith

lemma mellin_sieve_remainder_ratio {q N A δ κ z s j : ℝ}
    (hq : 2 ≤ q) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hNlo : q^10 ≤ N) (hNhi : N ≤ q^11)
    (_hz : 0 ≤ z) (hzq : z ≤ 2*q^κ) (hs : 0 ≤ s) (hsq : s ≤ q^κ)
    (hj : 0 ≤ j) (hjq : j ≤ 8*Real.log q) :
    z*(6*q^9+j*A*N^(1-δ))*s/N*Real.log N ≤ mellinSparseBudget A δ κ q := by
  have hq0 : 0 < q := by linarith
  have hN : 0 < N := (pow_pos hq0 10).trans_le hNlo
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg ((one_le_pow₀ (by linarith : 1 ≤ q)).trans hNlo)
  have hl : Real.log N ≤ 11*Real.log q := by
    have hh := Real.log_le_log hN hNhi
    rwa [Real.log_pow] at hh
  have hf : q^9/N ≤ q^(-1:ℝ) := by
    calc
      _ ≤ q^9/q^10 := div_le_div_of_nonneg_left (by positivity) (by positivity) hNlo
      _ = _ := by rw [← Real.rpow_natCast q 9, ← Real.rpow_natCast q 10, ← Real.rpow_sub hq0]; norm_num
  have hn : N^(1-δ)/N ≤ q^(-10*δ) := by
    have he : N^(1-δ)/N = N^(-δ) := by
      calc
        _ = N^(1-δ)/N^(1:ℝ) := by rw [Real.rpow_one]
        _ = N^((1-δ)-1) := (Real.rpow_sub hN _ _).symm
        _ = _ := by congr 1; ring
    rw [he]
    apply (Real.rpow_le_rpow_of_nonpos (pow_pos hq0 10) hNlo (by linarith)).trans_eq
    rw [← Real.rpow_natCast q 10, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have he : (6*q^9+j*A*N^(1-δ))/N ≤ 6*q^(-1:ℝ)+8*Real.log q*A*q^(-10*δ) := by
    calc
      _ = 6*(q^9/N)+(j*A)*(N^(1-δ)/N) := by ring
      _ ≤ 6*q^(-1:ℝ)+(8*Real.log q*A)*q^(-10*δ) := by
        apply add_le_add (mul_le_mul_of_nonneg_left hf (by norm_num))
        exact mul_le_mul (mul_le_mul_of_nonneg_right hjq hA) hn
          (by positivity) (by positivity)
      _ = _ := by ring
  have hzs : z*s ≤ 2*q^(2*κ) := by
    calc
      _ ≤ (2*q^κ)*q^κ := mul_le_mul hzq hsq hs (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hq0]; congr 2; ring
  have hE : 0 ≤ (6*q^9+j*A*N^(1-δ))/N := by positivity
  have hp1 : q^(2*κ)*q^(-1:ℝ) = q^(2*κ-1) := by rw [← Real.rpow_add hq0]; congr 1
  have hp2 : q^(2*κ)*q^(-10*δ) = q^(2*κ-10*δ) := by rw [← Real.rpow_add hq0]; congr 1; ring
  calc
    _ = (z*s)*((6*q^9+j*A*N^(1-δ))/N)*Real.log N := by ring
    _ ≤ (2*q^(2*κ))*(6*q^(-1:ℝ)+8*Real.log q*A*q^(-10*δ))*(11*Real.log q) :=
      mul_le_mul (mul_le_mul hzs he hE (by positivity)) hl hlogN (by positivity)
    _ = 132*(q^(2*κ)*q^(-1:ℝ))*Real.log q+
        176*A*(q^(2*κ)*q^(-10*δ))*(Real.log q)^2 := by ring
    _ = _ := by rw [hp1,hp2]; rfl

/-- The complete remainder is smaller than the prime-density scale for
sufficiently sparse samples and a correspondingly small sieve level. -/
theorem mellin_sieve_remainder_absorption (A : ℝ) (hA : 0 ≤ A)
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : κ ≤ 1/8) (hκδ : κ ≤ δ) :
    ∀ᶠ q : ℝ in atTop, ∀ N z s j : ℝ,
      q^10 ≤ N → N ≤ q^11 →
      0 ≤ z → z ≤ 2*q^κ → 0 ≤ s → s ≤ q^κ →
      0 ≤ j → j ≤ 8*Real.log q →
      z*(6*q^9+j*A*N^(1-δ))*s ≤ N/Real.log N := by
  have hlim := mellinSparseBudget_tendsto A hδ hκ hκδ
  filter_upwards [eventually_ge_atTop (2:ℝ), hlim.eventually (eventually_lt_nhds zero_lt_one)] with q hq hb
  intro N z s j hNlo hNhi hz hzq hs hsq hj hjq
  have hN1 : 1 < N := (one_lt_pow₀ (by linarith : 1 < q) (by norm_num : 10 ≠ 0)).trans_le hNlo
  have hratio := (mellin_sieve_remainder_ratio hq hA hδ hNlo hNhi hz hzq hs hsq hj hjq).trans hb.le
  apply (le_div_iff₀ (Real.log_pos hN1)).mpr
  apply (div_le_one (by linarith : 0 < N)).mp
  convert hratio using 1 <;> first | rfl | ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveLevel
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small prime-sieve level with quantitative logarithmic size -/
namespace JointDickman
open Filter
open scoped Topology

lemma mellin_small_sieve_level {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∀ᶠ q : ℝ in atTop,
      2 ≤ ⌊q^κ⌋₊ ∧ (⌊q^κ⌋₊ : ℝ) ≤ q ∧
      ((⌊q^κ⌋₊+1:ℕ):ℝ) ≤ 2*q^κ ∧
      (κ/2)*Real.log q ≤ Real.log (⌊q^κ⌋₊ : ℝ) := by
  have hp := (tendsto_rpow_atTop (show 0 < κ/2 by positivity)).eventually_ge_atTop 2
  filter_upwards [eventually_gt_atTop (1:ℝ),hp] with q hq hpow
  have hq0 : 0 < q := by linarith
  have he : (q^(κ/2))^2 = q^κ := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have hfloor : q^(κ/2) ≤ (⌊q^κ⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one (q^κ)
    nlinarith [sq_nonneg (q^(κ/2)-1)]
  have hfloor2 : 2 ≤ ⌊q^κ⌋₊ := by exact_mod_cast hpow.trans hfloor
  have hle := Nat.floor_le (Real.rpow_nonneg hq0.le κ)
  refine ⟨hfloor2, hle.trans ?_, ?_, ?_⟩
  · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hq.le hκ1
  · push_cast
    have hp1 : 1 ≤ q^κ := by
      rw [← he]
      nlinarith
    linarith
  · have hh := Real.log_le_log (Real.rpow_pos_of_pos hq0 _) hfloor
    rwa [Real.log_rpow hq0] at hh

lemma mellin_sieve_level_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun q : ℝ => (⌊q^κ⌋₊ : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hκ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SparsePrimeMellin
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse prime Mellin sampling in polynomial frequency ranges -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology Classical

/-- An unconditional prime-density sampling bound. The sparse sample
exponent may depend on the fixed polynomial frequency range. -/
theorem sparse_prime_mellin_sampling (B : ℝ) (hB : 1 ≤ B) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ q : ℕ in atTop, ∀ (N : ℝ) (Q : Finset ℕ) (S : Finset ℝ),
      (q:ℝ)^10 ≤ N → N ≤ (q:ℝ)^11 →
      (∀ p ∈ Q, p.Prime ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ (q:ℝ)^B) →
      (S.card:ℝ) ≤ (q:ℝ)^κ →
      ∀ a : ℕ → ℂ,
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q a (fun n => -Real.log (n:ℝ)) t‖^2) ≤
        C*N/Real.log N * ∑ p ∈ Q, ‖a p‖^2 := by
  obtain ⟨C,A,δ,V,hC,hA,hδ,hδ1,hbound⟩ := mellin_prime_sampling_arithmetic_jd B hB
  obtain ⟨D,hD,hprod⟩ := prime_survival_eventually_le
  let κ : ℝ := min (1/8) δ
  have hκ : 0 < κ := lt_min (by norm_num) hδ
  have hκ8 : κ ≤ 1/8 := min_le_left _ _
  have hκδ : κ ≤ δ := min_le_right _ _
  have hκ1 : κ ≤ 1 := hκ8.trans (by norm_num)
  let E : ℝ := 8*(32*C*(22*D/κ)+1)
  have hE : 0 < E := by dsimp [E] <;> positivity
  refine ⟨E,κ,hE,hκ,?_⟩
  have hlevel := tendsto_natCast_atTop_atTop.eventually (mellin_small_sieve_level hκ hκ1)
  have herr := tendsto_natCast_atTop_atTop.eventually
    (mellin_sieve_remainder_absorption A hA.le hδ hκ8 hκδ)
  have hp := ((mellin_sieve_level_tendsto hκ).comp tendsto_natCast_atTop_atTop).eventually hprod
  have hv := ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 9)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop V
  filter_upwards [eventually_ge_atTop 16,hlevel,herr,hp,hv] with q hq hlevel herr hp hv
  simp only [Function.comp_apply, Real.rpow_ofNat] at hv
  simp only [Function.comp_apply, Nat.floor_natCast] at hp
  intro N Q S hNlo hNhi hQ hsep hdiam hcard a
  let Z := ⌊(q:ℝ)^κ⌋₊
  let P := (Icc 2 Z).filter Nat.Prime
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hN1 : 1 < N := (one_lt_pow₀ (by linarith : (1:ℝ) < q) (by norm_num : 10 ≠ 0)).trans_le hNlo
  have hN0 : 0 < N := by linarith
  have hZ : 2 ≤ Z := hlevel.1
  have hZq : Z ≤ q := by exact_mod_cast hlevel.2.1
  have hP : ∀ p ∈ P, p.Prime ∧ p ≤ Z := by
    intro p hp
    exact ⟨(mem_filter.mp hp).2, (mem_Icc.mp (mem_filter.mp hp).1).2⟩
  have hQN : ∀ p ∈ Q, p.Prime ∧ Z < p ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N := by
    intro p hp
    have hpow : (q:ℝ) < (q:ℝ)^10 := by
      have hh := pow_le_pow_right₀ hq1 (show 2 ≤ 10 by norm_num)
      nlinarith
    have hZp : (Z:ℝ) < p := hlevel.2.1.trans_lt (hpow.trans_le (hNlo.trans (hQ p hp).2.1))
    exact ⟨(hQ p hp).1, by exact_mod_cast hZp, (hQ p hp).2⟩
  have hs := hbound q Z P Q N S hq hZ hZq hv hNlo hNhi hP hQN hsep hdiam a
  have herror := herr N (↑(Z+1)) S.card (↑(Nat.log 2 (q^3)+1)) hNlo hNhi
    (by positivity) hlevel.2.2.1 (by positivity) hcard (by positivity)
    (mellin_dyadic_count_le (by omega))
  have hlogZ : (κ/22)*Real.log N ≤ Real.log (Z:ℝ) := by
    have hl := Real.log_le_log hN0 hNhi
    rw [Real.log_pow] at hl
    have hzlog : (κ/2)*Real.log (q:ℝ) ≤ Real.log (Z:ℝ) := hlevel.2.2.2
    norm_num only [Nat.cast_ofNat] at hl
    nlinarith
  have hlogZ0 : 0 < Real.log (Z:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hlogN0 := Real.log_pos hN1
  have hPbound : (∏ p ∈ P, (1-1/(p:ℝ))) ≤ (22*D/κ)/Real.log N := by
    have hp' : (∏ p ∈ P, (1-1/(p:ℝ))) ≤ D/Real.log (Z:ℝ) := by
      simpa only [Nat.floor_natCast] using hp
    apply hp'.trans
    apply (div_le_div_iff₀ hlogZ0 hlogN0).mpr
    have hh := mul_le_mul_of_nonneg_left hlogZ (show 0 ≤ 22*D/κ by positivity)
    have he : (22*D/κ)*((κ/22)*Real.log N) = D*Real.log N := by field_simp
    rw [he] at hh
    exact hh
  apply hs.trans
  have hmain : 32*C*N*(∏ p ∈ P, (1-1/(p:ℝ))) ≤ 32*C*(22*D/κ)*(N/Real.log N) := by
    apply (mul_le_mul_of_nonneg_left hPbound (by positivity : 0 ≤ 32*C*N)).trans_eq
    ring
  have htotal : 8*(32*C*N*(∏ p ∈ P, (1-1/(p:ℝ))) + (Z+1:ℕ)*
      (6*(q:ℝ)^9+(Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ))*S.card) ≤ E*N/Real.log N := by
    dsimp only [E]
    calc
      _ ≤ 8*(32*C*(22*D/κ)*(N/Real.log N)+N/Real.log N) :=
        mul_le_mul_of_nonneg_left (add_le_add hmain herror) (by norm_num)
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right htotal (sum_nonneg (fun _ _ => sq_nonneg _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeReciprocalSquareMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal-square mass of a dyadic prime interval -/
namespace JointDickman
open Finset

/-- Chebyshev's proved prime bound supplies the second logarithmic saving
when sparse sampling is applied to a reciprocal prime polynomial. -/
theorem prime_reciprocal_square_mass : ∃ D : ℝ, 0 < D ∧
    ∀ (N : ℝ), 2 ≤ N → ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∑ p ∈ Q, 1/(p:ℝ)^2) ≤ D/(N*Real.log N) := by
  obtain ⟨C,hC,hcount⟩ := chebyshevPrimeCountingInput
  refine ⟨2*(C+1),by positivity,?_⟩
  intro N hN Q hQ
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog2 : Real.log N ≤ Real.log (2*N) :=
    Real.log_le_log hN0 (by linarith)
  have hcard : (Q.card:ℝ) ≤ C*(2*N)/Real.log (2*N) := by
    apply le_trans (b := (Nat.primeCounting ⌊2*N⌋₊:ℝ))
    · rw [← Nat.primesLE_card_eq_primeCounting]
      exact_mod_cast card_le_card (show Q ⊆ Nat.primesLE ⌊2*N⌋₊ by
        intro p hp
        exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hQ p hp).2.2, (hQ p hp).1⟩)
    · exact hcount (2*N) (by linarith)
  have hcard' : (Q.card:ℝ) ≤ 2*C*N/Real.log N := by
    exact hcard.trans (by
      rw [show C*(2*N)=2*C*N by ring]
      exact div_le_div_of_nonneg_left (by positivity) hlog hlog2)
  calc
    _ ≤ ∑ _p ∈ Q, 1/N^2 := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le (sq_pos_of_pos hN0)
        (pow_le_pow_left₀ hN0.le (hQ p hp).2.1 2)
    _ = (Q.card:ℝ)/N^2 := by simp [div_eq_mul_inv]
    _ ≤ (2*C*N/Real.log N)/N^2 := div_le_div_of_nonneg_right hcard' (sq_nonneg N)
    _ = 2*C/(N*Real.log N) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SparsePrimeReciprocal
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse reciprocal-prime polynomials and their two logarithmic savings -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

/-- The prime density in both the sampling matrix and its coefficient mass
gives the squared-logarithm saving required for the exceptional class. -/
theorem sparse_prime_reciprocal_sampling (B : ℝ) (hB : 1 ≤ B) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ q : ℕ in atTop, ∀ (N : ℝ) (Q : Finset ℕ) (S : Finset ℝ),
      (q:ℝ)^10 ≤ N → N ≤ (q:ℝ)^11 →
      (∀ p ∈ Q, p.Prime ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ (q:ℝ)^B) →
      (S.card:ℝ) ≤ (q:ℝ)^κ →
      ∀ f : ℕ → ℂ, OneBounded f →
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun n => -Real.log (n:ℝ)) t‖^2) ≤ C/(Real.log N)^2 := by
  obtain ⟨C,κ,hC,hκ,hbound⟩ := sparse_prime_mellin_sampling B hB
  obtain ⟨D,hD,hmass⟩ := prime_reciprocal_square_mass
  refine ⟨C*D,κ,mul_pos hC hD,hκ,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 2] with q hq hq2
  intro N Q S hNlo hNhi hQ hsep hdiam hcard f hf
  have hqr : (2:ℝ) ≤ q := by exact_mod_cast hq2
  have hN2 : 2 ≤ N := by
    have hh : (q:ℝ) ≤ (q:ℝ)^10 := le_self_pow₀ (by linarith) (by norm_num)
    exact hqr.trans (hh.trans hNlo)
  have hN0 : 0 < N := by linarith
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hm : (∑ p ∈ Q, ‖f p/(p:ℂ)‖^2) ≤ D/(N*Real.log N) := by
    apply le_trans (b := ∑ p ∈ Q, 1/(p:ℝ)^2)
    · apply sum_le_sum
      intro p hp
      rw [norm_div, Complex.norm_natCast, div_pow]
      exact div_le_div_of_nonneg_right
        (by nlinarith [hf p (hQ p hp).1.pos, norm_nonneg (f p)]) (sq_nonneg _)
    · exact hmass N hN2 Q hQ
  apply (hq N Q S hNlo hNhi hQ hsep hdiam hcard _).trans
  calc
    _ ≤ C*N/Real.log N*(D/(N*Real.log N)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinRealScale
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing the sparse prime estimate from integer to real scales -/
namespace JointDickman
open Filter Finset TwoPointCorrelations
open scoped Topology

lemma floor_rpow_eventually_lower {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, x^a ≤ (⌊x^b⌋₊:ℝ) := by
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (1:ℝ),hg] with x hx hg
  have hx0 : 0 < x := by linarith
  have ha1 : 1 ≤ x^a := Real.one_le_rpow hx ha.le
  have he : x^b = x^a*x^(b-a) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hf := Nat.lt_floor_add_one (x^b)
  have hh : 2*x^a ≤ x^b := by rw [he]; nlinarith
  nlinarith

lemma mellin_real_scale_eventually : ∀ᶠ x : ℝ in atTop,
    let q := ⌊x^((1:ℝ)/10)⌋₊
    2 ≤ q ∧ (q:ℝ)^10 ≤ x ∧ x ≤ (q:ℝ)^11 ∧ x^((1:ℝ)/20) ≤ (q:ℝ) := by
  have h11 := floor_rpow_eventually_lower (a := (1:ℝ)/11) (b := 1/10)
    (by norm_num) (by norm_num)
  have h20 := floor_rpow_eventually_lower (a := (1:ℝ)/20) (b := 1/10)
    (by norm_num) (by norm_num)
  have hg := (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10))).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (1:ℝ),h11,h20,hg] with x hx h11 h20 hg
  dsimp only
  have hx0 : 0 < x := by linarith
  refine ⟨hg,?_,?_,h20⟩
  · have hf := Nat.floor_le (Real.rpow_nonneg hx0.le ((1:ℝ)/10))
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg ⌊x^((1:ℝ)/10)⌋₊) hf 10
    have he : (x^((1:ℝ)/10))^10=x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rwa [he] at hh
  · have hh := pow_le_pow_left₀ (Real.rpow_nonneg hx0.le ((1:ℝ)/11)) h11 11
    have he : (x^((1:ℝ)/11))^11=x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rwa [he] at hh

/-- Arbitrary sufficiently large real prime lengths are allowed; the
integer auxiliary scale is no longer visible to applications. -/
theorem sparse_prime_reciprocal_real (B : ℝ) (hB : 1 ≤ B) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ᶠ N : ℝ in atTop, ∀ (Q : Finset ℕ) (S : Finset ℝ),
      (∀ p ∈ Q, p.Prime ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ N^B) →
      (S.card:ℝ) ≤ N^γ →
      ∀ f : ℕ → ℂ, OneBounded f →
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun n => -Real.log (n:ℝ)) t‖^2) ≤ C/(Real.log N)^2 := by
  obtain ⟨C,κ,hC,hκ,hbound⟩ := sparse_prime_reciprocal_sampling (20*B) (by linarith)
  refine ⟨C,κ/20,hC,by positivity,?_⟩
  have hscale : Tendsto (fun x : ℝ => ⌊x^((1:ℝ)/10)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num))
  filter_upwards [mellin_real_scale_eventually,hscale.eventually hbound,
    eventually_ge_atTop (1:ℝ)] with N hscale hbound hN
  let q := ⌊N^((1:ℝ)/10)⌋₊
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hN0 : 0 < N := by linarith
  intro Q S hQ hsep hdiam hcard f hf
  apply hbound N Q S hscale.2.1 hscale.2.2.1 hQ hsep _ _ f hf
  · intro x hx y hy
    apply (hdiam x hx y hy).trans
    calc
      N^B = (N^((1:ℝ)/20))^(20*B) := by
        rw [← Real.rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ (q:ℝ)^(20*B) := Real.rpow_le_rpow (by positivity) hscale.2.2.2 (by linarith)
  · apply hcard.trans
    calc
      N^(κ/20) = (N^((1:ℝ)/20))^κ := by
        rw [← Real.rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ (q:ℝ)^κ := Real.rpow_le_rpow (by positivity) hscale.2.2.2 hκ.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseFirstDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A first-derivative bound for short logarithmic phase sums -/
namespace JointDickman
open Finset Problem337

lemma log_step_bounds {x : ℝ} (hx : 0 < x) :
    1/(x+1) ≤ Real.log (x+1)-Real.log x ∧
      Real.log (x+1)-Real.log x ≤ 1/x := by
  have hx1 : 0 < x+1 := by positivity
  rw [← Real.log_div hx1.ne' hx.ne']
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  · have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring

lemma log_step_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log (y+1)-Real.log y ≤ Real.log (x+1)-Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  rw [← Real.log_div (by positivity : x+1 ≠ 0) hx.ne',
    ← Real.log_div (by positivity : y+1 ≠ 0) hy.ne']
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ hy hx).mpr
  nlinarith

/-- Below the first stationary range the sharp logarithmic sum is bounded
by the reciprocal frequency, with no length-dependent error. -/
theorem positive_log_phase_first_bound {U Z : ℝ} (hU : 1 ≤ U)
    (hZ : 0 < Z) (hZU : Z ≤ U/4) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤ 8*U/Z := by
  have hU0 : 0 < U := by linarith
  have hβ : 0 < Z/(4*U) := by positivity
  have hd (i : ℕ) (hiL : L ≤ i) (hiR : i ≤ R) :
      Z/(4*U) ≤ Z*Real.log ((i+1:ℕ):ℝ)-Z*Real.log (i:ℝ) ∧
      Z*Real.log ((i+1:ℕ):ℝ)-Z*Real.log (i:ℝ) ≤ 1-Z/(4*U) := by
    have hi : U ≤ (i:ℝ) := hL.trans (by exact_mod_cast hiL)
    have hi2 : (i:ℝ) ≤ 2*U := (by exact_mod_cast hiR : (i:ℝ) ≤ R).trans hR
    have hi0 : (0:ℝ) < i := hU0.trans_le hi
    obtain ⟨hlo,hhi⟩ := log_step_bounds hi0
    push_cast
    rw [← mul_sub]
    constructor
    · apply (div_le_div_of_nonneg_left hZ.le (by positivity : (0:ℝ) < i+1)
        (by linarith : (i:ℝ)+1 ≤ 4*U)).trans
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hlo hZ.le
    · have hu : Z*((1:ℝ)/i) ≤ Z/U := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left hZ.le hU0 hi
      have hh : Z/U ≤ 1/4 := (div_le_iff₀ hU0).mpr (by linarith)
      have hb : Z/(4*U) ≤ 1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hhi hZ.le]
  have hmono : AntitoneOn (fun i : ℕ => Z*Real.log ((i+1:ℕ):ℝ)-
      Z*Real.log (i:ℝ)) (Set.Icc L R) := by
    intro i hi j _ hij
    push_cast
    rw [← mul_sub, ← mul_sub]
    apply mul_le_mul_of_nonneg_left _ hZ.le
    exact log_step_antitone (hU0.trans_le (hL.trans (by exact_mod_cast hi.1)))
      (by exact_mod_cast hij)
  have hh := ExponentialSum.first_derivative_sum_bound_Icc
    (fun n => Z*Real.log (n:ℝ)) L R (Z/(4*U)) 0 hβ
    (fun i hiL hiR => by simpa using (hd i hiL hiR).1)
    (fun i hiL hiR => by simpa using (hd i hiL hiR).2) (Or.inr hmono)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  norm_num

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseSharpBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sharp dyadic logarithmic sums in the first two derivative ranges -/
namespace JointDickman
open Finset Problem337
open scoped ComplexConjugate

lemma log_phase_sum_neg (Z : ℝ) (L R : ℕ) :
    (∑ n ∈ Icc L R, ExponentialSum.phase (-Z*Real.log (n:ℝ))) =
      conj (∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))) := by
  simp only [map_sum, neg_mul, ExponentialSum.phase_neg]

lemma log_phase_sum_trivial {U : ℝ} (hU : 1 ≤ U) (Z : ℝ) (L R : ℕ)
    (hR : (R:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤ 3*U := by
  calc
    _ ≤ ∑ n ∈ Icc L R, ‖ExponentialSum.phase (Z*Real.log (n:ℝ))‖ := norm_sum_le _ _
    _ = ((Icc L R).card:ℝ) := by simp only [ExponentialSum.phase_norm, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (R:ℝ)+1 := by
      exact_mod_cast (show (Icc L R).card ≤ R+1 by rw [Nat.card_Icc]; omega)
    _ ≤ 3*U := by linarith

lemma log_phase_second_bound {U Z : ℝ} (hU : 1 ≤ U)
    (hZ : U/4 ≤ |Z|) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤
      2000*Real.sqrt |Z| := by
  have hU0 : 0 < U := by linarith
  have hZ0 : 0 < |Z| := by linarith
  by_cases hLR : L ≤ R
  · let N := R+1-L
    have hN : (L:ℝ)+(N:ℝ) = (R:ℝ)+1 := by
      exact_mod_cast (show L+N=R+1 by dsimp [N]; omega)
    have hNle : (N:ℝ) ≤ 2*U := by linarith
    have hh := logarithmic_difference_sum_bound [] (by simp) 0 Z U L N
      (abs_pos.mp hZ0) hU0 hL (by simp only [List.sum_nil, add_zero] <;> linarith)
    simp only [List.prod_nil, List.length_nil, zero_add, Nat.factorial_one,
      Nat.cast_one, one_mul, forwardDifference, zero_mul] at hh
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hh
    have hs : Real.sqrt (|Z|/(4*U)^2) = Real.sqrt |Z|/(4*U) := by
      rw [Real.sqrt_div (abs_nonneg _), Real.sqrt_sq (by positivity)]
    rw [hs] at hh
    have hsq : (Real.sqrt |Z|)^2 = |Z| := Real.sq_sqrt hZ0.le
    have hsqrt : 0 < Real.sqrt |Z| := Real.sqrt_pos.mpr hZ0
    have hn : (N:ℝ)*(Real.sqrt |Z|/(4*U)) ≤ Real.sqrt |Z| := by
      calc
        _ = ((N:ℝ)/(4*U))*Real.sqrt |Z| := by ring
        _ ≤ 1*Real.sqrt |Z| := mul_le_mul_of_nonneg_right
          ((div_le_one (by positivity)).mpr (by linarith)) (Real.sqrt_nonneg |Z|)
        _ = _ := one_mul _
    have hi : 1/(Real.sqrt |Z|/(4*U)) ≤ 16*Real.sqrt |Z| := by
      rw [one_div_div]
      apply (div_le_iff₀ hsqrt).mpr
      nlinarith
    have hset : Icc L R = Ico L (R+1) := by ext n; simp
    rw [hset, sum_Ico_eq_sum_range]
    have he : (∑ k ∈ range (R+1-L), ExponentialSum.phase (Z*Real.log ((L+k:ℕ):ℝ))) =
        ∑ j ∈ range N, ExponentialSum.phase (Z*Real.log ((j:ℝ)+(L:ℝ))) := by
      apply sum_congr rfl
      intro j _
      simp only [Nat.cast_add, add_comm]
    rw [he]
    apply hh.trans
    nlinarith
  · rw [Icc_eq_empty (by omega), sum_empty, norm_zero]
    positivity

/-- Uniform sharp-interval estimate. The square-root term is used only
above the first derivative range. -/
theorem log_phase_sharp_bound {U : ℝ} (hU : 1 ≤ U) (Z : ℝ) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤
      2000*(U/(1+|Z|)+Real.sqrt |Z|) := by
  have hU0 : 0 < U := by linarith
  by_cases hz : |Z| ≤ 1
  · have hu : 3*U ≤ 2000*(U/(1+|Z|)+Real.sqrt |Z|) := by
      have hd : U/2 ≤ U/(1+|Z|) :=
        div_le_div_of_nonneg_left hU0.le (by positivity) (by linarith)
      nlinarith [Real.sqrt_nonneg |Z|]
    exact (log_phase_sum_trivial hU Z L R hR).trans hu
  · by_cases hhi : U/4 ≤ |Z|
    · apply (log_phase_second_bound hU hhi L R hL hR).trans
      have hd : 0 ≤ U/(1+|Z|) := by positivity
      nlinarith
    · have hpos : 0 < |Z| := lt_trans zero_lt_one (lt_of_not_ge hz)
      have hh : ‖∑ n ∈ Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤ 8*U/|Z| := by
        by_cases hp : 0 ≤ Z
        · simpa only [abs_of_nonneg hp] using
            positive_log_phase_first_bound hU (by simpa only [abs_of_nonneg hp] using hpos)
              (by simpa only [abs_of_nonneg hp] using le_of_not_ge hhi) L R hL hR
        · have hn : |Z| = -Z := abs_of_neg (lt_of_not_ge hp)
          have hh := positive_log_phase_first_bound hU hpos (le_of_not_ge hhi) L R hL hR
          rw [hn, log_phase_sum_neg, Complex.norm_conj] at hh
          simpa only [hn] using hh
      apply hh.trans
      have hd : U/|Z| ≤ 2*(U/(1+|Z|)) := by
        rw [show 2*(U/(1+|Z|)) = (2*U)/(1+|Z|) by ring]
        apply (div_le_div_iff₀ hpos (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_left (show 1+|Z| ≤ 2*|Z| by linarith) hU0.le]
      have hd0 : 0 ≤ U/(1+|Z|) := by positivity
      calc
        _ = 8*(U/|Z|) := by ring
        _ ≤ 8*(2*(U/(1+|Z|))) := mul_le_mul_of_nonneg_left hd (by norm_num)
        _ ≤ _ := by nlinarith [Real.sqrt_nonneg |Z|]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SeparatedHarmonicKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic-decay kernels on separated samples -/
namespace JointDickman
open Finset
open scoped Classical

private lemma interval_sample_card (S : Finset ℝ) (x : ℝ → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |x i-x j|) (b : ℝ) :
    (S.filter (fun i => b ≤ x i ∧ x i < b+1)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiS,hi⟩ := mem_filter.mp hi
  obtain ⟨hjS,hj⟩ := mem_filter.mp hj
  by_contra hne
  have hh := hsep i hiS j hjS hne
  have ht : |x i-x j| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

private lemma absolute_sample_card (S : Finset ℝ) (x : ℝ → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |x i-x j|) (b : ℝ) :
    (S.filter (fun i => b ≤ |x i| ∧ |x i| < b+1)).card ≤ 2 := by
  let P := S.filter (fun i => b ≤ x i ∧ x i < b+1)
  let Q := S.filter (fun i => b ≤ -x i ∧ -x i < b+1)
  have hp : P.card ≤ 1 := interval_sample_card S x hsep b
  have hq : Q.card ≤ 1 := interval_sample_card S (fun i => -x i)
    (by intro i hi j hj hne; simpa only [neg_sub_neg, abs_sub_comm] using hsep i hi j hj hne) b
  have hsub : S.filter (fun i => b ≤ |x i| ∧ |x i| < b+1) ⊆ P ∪ Q := by
    intro i hi
    obtain ⟨hiS,hi⟩ := mem_filter.mp hi
    by_cases hx : 0 ≤ x i
    · exact mem_union_left Q (mem_filter.mpr ⟨hiS, by simpa only [abs_of_nonneg hx] using hi⟩)
    · exact mem_union_right P (mem_filter.mpr ⟨hiS, by simpa only [abs_of_neg (lt_of_not_ge hx)] using hi⟩)
  have hu := (card_le_card hsub).trans (card_union_le P Q)
  omega

/-- Harmonic row sums grow only logarithmically with the diameter of the
sample set. The proof uses at most two points in each absolute unit band. -/
theorem separated_harmonic_kernel_sum (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    (t T : ℝ) (hT : 0 ≤ T) (hdiam : ∀ u ∈ S, |t-u| ≤ T) :
    (∑ u ∈ S, 1/(1+|t-u|)) ≤ 2*(1+Real.log (T+1)) := by
  let b : ℝ → ℕ := fun u => ⌊|t-u|⌋₊
  let K := ⌊T⌋₊
  let F : ℕ → Finset ℝ := fun j => S.filter (fun u => b u=j)
  have hpart : (∑ u ∈ S, 1/(1+|t-u|)) =
      ∑ j ∈ range (K+1), ∑ u ∈ F j, 1/(1+|t-u|) := by
    symm
    apply sum_fiberwise_of_maps_to
    intro u hu
    apply mem_range.mpr
    have hh : b u ≤ K := Nat.floor_le_floor (hdiam u hu)
    omega
  have hband (j : ℕ) (u : ℝ) (hu : u ∈ F j) :
      (j:ℝ) ≤ |t-u| ∧ |t-u| < (j:ℝ)+1 := by
    have he := (mem_filter.mp hu).2
    have hl := Nat.floor_le (abs_nonneg (t-u))
    have hh := Nat.lt_floor_add_one |t-u|
    change (b u:ℝ) ≤ |t-u| at hl
    change |t-u| < (b u:ℝ)+1 at hh
    rw [he] at hl hh
    exact ⟨hl,hh⟩
  have hc (j : ℕ) : (F j).card ≤ 2 := by
    apply (card_le_card (s := F j) (t := S.filter
      (fun u => (j:ℝ) ≤ |t-u| ∧ |t-u| < (j:ℝ)+1)) ?_).trans
      (absolute_sample_card S (fun u => t-u)
        (by intro u hu v hv hne; simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hsep u hu v hv hne) j)
    intro u hu
    exact mem_filter.mpr ⟨(mem_filter.mp hu).1,hband j u hu⟩
  have hj (j : ℕ) : (∑ u ∈ F j, 1/(1+|t-u|)) ≤ 2/(1+(j:ℝ)) := by
    calc
      _ ≤ ∑ _u ∈ F j, 1/(1+(j:ℝ)) := sum_le_sum fun u hu =>
        one_div_le_one_div_of_le (by positivity) (by linarith [(hband j u hu).1])
      _ = ((F j).card:ℝ)/(1+(j:ℝ)) := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hc j) (by positivity)
  rw [hpart]
  apply (sum_le_sum fun j _ => hj j).trans
  have he : (∑ j ∈ range (K+1), 2/(1+(j:ℝ))) = 2*(harmonic (K+1):ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one,
      Rat.cast_natCast, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_sum]
    apply sum_congr rfl
    intro j _
    rw [add_comm]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (harmonic_le_one_add_log (K+1)).trans
  have hk : ((K+1:ℕ):ℝ) ≤ T+1 := by
    push_cast
    exact add_le_add (Nat.floor_le hT) le_rfl
  gcongr

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinIntegerKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer Mellin kernel on a dyadic interval -/
namespace JointDickman
open Finset Problem337 TwoPointCorrelations

lemma mellin_integer_kernel_phase (L R : ℕ) (t : ℝ) :
    mellinSampleKernel (Icc L R) (fun _ => 1) t =
      ∑ n ∈ Icc L R, ExponentialSum.phase ((-t/(2*Real.pi))*Real.log (n:ℝ)) := by
  unfold mellinSampleKernel ExponentialSum.phase
  apply sum_congr rfl
  intro n _
  simp only [Complex.ofReal_one, one_mul]
  congr 2
  push_cast
  field_simp

/-- A sharp dyadic Mellin kernel has reciprocal decay below its length,
and a square-root error beyond it. -/
theorem mellin_integer_kernel_bound {U : ℝ} (hU : 1 ≤ U) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U) (t : ℝ) :
    ‖mellinSampleKernel (Icc L R) (fun _ => 1) t‖ ≤
      16000*(U/(1+|t|)+Real.sqrt |t|) := by
  have hp : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hp8 : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
  have hp0 : 0 < 2*Real.pi := by positivity
  have habs : |-t/(2*Real.pi)| = |t|/(2*Real.pi) := by
    rw [abs_div, abs_neg, abs_of_pos hp0]
  have hd : U/(1+|t|/(2*Real.pi)) ≤ (2*Real.pi)*(U/(1+|t|)) := by
    rw [show (2*Real.pi)*(U/(1+|t|)) = ((2*Real.pi)*U)/(1+|t|) by ring]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have he : (2*Real.pi)*U*(1+|t|/(2*Real.pi)) = U*(2*Real.pi+|t|) := by field_simp
    rw [he]
    nlinarith
  have hs : Real.sqrt (|t|/(2*Real.pi)) ≤ Real.sqrt |t| := by
    apply Real.sqrt_le_sqrt
    exact div_le_self (abs_nonneg t) hp
  rw [mellin_integer_kernel_phase]
  have hh := log_phase_sharp_bound hU (-t/(2*Real.pi)) L R hL hR
  rw [habs] at hh
  apply hh.trans
  have hd0 : 0 ≤ U/(1+|t|) := by positivity
  have hsq0 := Real.sqrt_nonneg |t|
  nlinarith

/-- The concrete sharp integer kernel has a logarithmic row bound, plus
a cost proportional to the number of sampled frequencies. -/
theorem mellin_integer_kernel_rows {U : ℝ} (hU : 1 ≤ U) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U)
    (S : Finset ℝ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    {T : ℝ} (hT : 0 ≤ T)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T) (t : ℝ) (ht : t ∈ S) :
    (∑ u ∈ S, ‖mellinSampleKernel (Icc L R) (fun _ => 1) (t-u)‖) ≤
      16000*(2*U*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T) := by
  calc
    _ ≤ ∑ u ∈ S, 16000*(U/(1+|t-u|)+Real.sqrt T) := by
      apply sum_le_sum
      intro u hu
      apply (mellin_integer_kernel_bound hU L R hL hR (t-u)).trans
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (Real.sqrt_le_sqrt (hdiam t ht u hu))) (by norm_num)
    _ = 16000*(U*(∑ u ∈ S, 1/(1+|t-u|))+(S.card:ℝ)*Real.sqrt T) := by
      simp only [div_eq_mul_inv, mul_add, mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
      ring_nf
    _ ≤ _ := by
      have hh := separated_harmonic_kernel_sum S hsep t T hT (hdiam t ht)
      nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SparseIntegerMellin
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse sampling of the actual integer cofactor polynomial -/
namespace JointDickman
open Finset TwoPointCorrelations

/-- Finite duality for sharp integer intervals, with the square-root
frequency error charged only once per sampled point. -/
theorem sparse_integer_mellin_sampling {U : ℝ} (hU : 1 ≤ U) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U)
    (S : Finset ℝ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    {T : ℝ} (hT : 0 ≤ T) (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T)
    (a : ℕ → ℂ) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial (Icc L R) a
      (fun n => -Real.log (n:ℝ)) t‖^2) ≤
      16000*(2*U*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T)*
        ∑ n ∈ Icc L R, ‖a n‖^2 := by
  have hlog : 0 ≤ Real.log (T+1) := Real.log_nonneg (by linarith)
  apply mellin_samples_of_dual _ S a (by positivity)
  intro b
  simpa only [one_mul] using mellin_weighted_dual_rows (Icc L R) S (fun _ => 1)
    (mellin_integer_kernel_rows hU L R hL hR S hsep hT hdiam) b

lemma reciprocal_cofactor_mass {U : ℝ} (hU : 1 ≤ U) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Icc L R, ‖a n‖ ≤ 1/(n:ℝ)) :
    (∑ n ∈ Icc L R, ‖a n‖^2) ≤ 3/U := by
  have hU0 : 0 < U := by linarith
  have hm : (∑ n ∈ Icc L R, ‖a n‖^2) ≤ ((Icc L R).card:ℝ)/U^2 := by
    calc
      _ ≤ ∑ _n ∈ Icc L R, (1/U)^2 := by
        apply sum_le_sum
        intro n hn
        have hnU : U ≤ (n:ℝ) := hL.trans (by exact_mod_cast (mem_Icc.mp hn).1)
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (ha n hn).trans (one_div_le_one_div_of_le hU0 hnU)
      _ = _ := by simp only [sum_const, nsmul_eq_mul] <;> ring
  have hc : ((Icc L R).card:ℝ) ≤ 3*U := by
    have hh : ((Icc L R).card:ℝ) ≤ (R:ℝ)+1 := by
      exact_mod_cast (show (Icc L R).card ≤ R+1 by rw [Nat.card_Icc]; omega)
    linarith
  calc
    _ ≤ ((Icc L R).card:ℝ)/U^2 := hm
    _ ≤ 3*U/U^2 := div_le_div_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by field_simp

/-- The normalized cofactor estimate required in the small-prime class of
the exceptional-frequency decomposition. Coefficients may already include
finite-prime masks and the reciprocal prime-count weight. -/
theorem sparse_reciprocal_cofactor_sampling {U : ℝ} (hU : 1 ≤ U) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U)
    (S : Finset ℝ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    {T : ℝ} (hT : 0 ≤ T) (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Icc L R, ‖a n‖ ≤ 1/(n:ℝ)) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial (Icc L R) a
      (fun n => -Real.log (n:ℝ)) t‖^2) ≤
      48000*(2*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T/U) := by
  have hlog : 0 ≤ Real.log (T+1) := Real.log_nonneg (by linarith)
  have hh := sparse_integer_mellin_sampling hU L R hL hR S hsep hT hdiam a
  apply hh.trans
  calc
    _ ≤ 16000*(2*U*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T)*(3/U) :=
      mul_le_mul_of_nonneg_left (reciprocal_cofactor_mass hU L R hL hR a ha) (by positivity)
    _ = _ := by field_simp <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SparseCofactorSampling
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse sampling for the reciprocal-count cofactor used by Ramaré -/
namespace JointDickman
open Finset TwoPointCorrelations

/-- The sparse integer estimate applies to the literal cofactor, including
all bounded coefficient masks and the reciprocal prime-divisor count. -/
theorem sparse_ramare_cofactor_sampling (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    {T : ℝ} (hT : 0 ≤ T) (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T) :
    (∑ t ∈ S, ‖mrtCofactorPolynomial P F N a t‖^2) ≤
      48000*(2*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T*a/N) := by
  let L := ⌊(N:ℝ)/a⌋₊+1
  let R := ⌊(2*N:ℝ)/a⌋₊
  have ha0 : 0 < a := by linarith
  have hU0 : 0 < (N:ℝ)/a := by linarith
  have hL : (N:ℝ)/a ≤ (L:ℝ) := by
    simpa only [L, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one ((N:ℝ)/a)).le
  have hR : (R:ℝ) ≤ 2*((N:ℝ)/a) := by
    change (⌊(2*N:ℝ)/a⌋₊:ℝ) ≤ _
    exact (Nat.floor_le (by positivity)).trans_eq (by ring)
  have hcoeff := mrt_reciprocal_count_oneBounded P F hF
  have hh := sparse_reciprocal_cofactor_sampling (U := (N:ℝ)/a) (by linarith)
    L R hL hR S hsep hT hdiam
    (fun n => (F n / ((finitePrimeDivisorCount P n + 1:ℕ):ℂ))/(n:ℂ)) (by
      intro n hn
      have hn0 : 0 < n := by
        have hl : 0 < L := by dsimp [L]; omega
        exact hl.trans_le (mem_Icc.mp hn).1
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (hcoeff n hn0) (Nat.cast_nonneg n))
  have he (t : ℝ) : mrtCofactorPolynomial P F N a t =
      mrtExponentialPolynomial (Icc L R)
        (fun n => (F n / ((finitePrimeDivisorCount P n + 1:ℕ):ℂ))/(n:ℂ))
        (fun n => -Real.log (n:ℝ)) t := by
    rw [mrt_cofactor_exponential_polynomial P F N ha]
    congr 1
    ext n
    simp only [mem_Ioc, mem_Icc, L, R]
    omega
  simp_rw [he]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinProductSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the small and large auxiliary prime values -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

/-- Split the finite product energy at the prime-polynomial threshold.
Only the large-prime class needs the pointwise cofactor bound. -/
lemma mellin_product_sample_split (S : Finset ℝ) (Q R : ℝ → ℂ)
    {τ b : ℝ} (_hτ : 0 ≤ τ)
    (hR : ∀ t ∈ S, τ < ‖Q t‖ → ‖R t‖ ≤ b) :
    (∑ t ∈ S, ‖Q t*R t‖^2) ≤
      τ^2*(∑ t ∈ S, ‖R t‖^2)+
        b^2*(∑ t ∈ S.filter (fun t => τ < ‖Q t‖), ‖Q t‖^2) := by
  let E := S.filter (fun t => τ < ‖Q t‖)
  have he : (∑ t ∈ S, ‖Q t*R t‖^2) =
      (∑ t ∈ E, ‖Q t*R t‖^2)+
        (∑ t ∈ S.filter (fun t => ¬τ < ‖Q t‖), ‖Q t*R t‖^2) := by
    exact (sum_filter_add_sum_filter_not S (fun t => τ < ‖Q t‖) _).symm
  have hlarge : (∑ t ∈ E, ‖Q t*R t‖^2) ≤ b^2*∑ t ∈ E, ‖Q t‖^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro t ht
    rw [norm_mul, mul_pow, mul_comm (b^2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hR t (mem_filter.mp ht).1 (mem_filter.mp ht).2) 2)
      (sq_nonneg _)
  have hsmall : (∑ t ∈ S.filter (fun t => ¬τ < ‖Q t‖), ‖Q t*R t‖^2) ≤
      τ^2*∑ t ∈ S, ‖R t‖^2 := by
    apply le_trans (b := τ^2*∑ t ∈ S.filter (fun t => ¬τ < ‖Q t‖), ‖R t‖^2)
    · rw [mul_sum]
      apply sum_le_sum
      intro t ht
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (le_of_not_gt (mem_filter.mp ht).2) 2)
        (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)) (sq_nonneg τ)
  rw [he]
  linarith

/-- Auxiliary-prime sampling in terms of sample counts and cofactor values. -/
theorem ramare_product_sparse_samples (B : ℝ) (hB : 1 ≤ B) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ᶠ a : ℝ in atTop, ∀ (N : ℕ) (P Q : Finset ℕ) (F f : ℕ → ℂ),
      1 ≤ a → 2 ≤ (N:ℝ)/a → OneBounded F → OneBounded f →
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ (S : Finset ℝ) (T τ b : ℝ), 0 ≤ T → 0 ≤ τ →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T) → T ≤ a^B →
      let Qf := mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ))
      ((S.filter (fun t => τ < ‖Qf t‖)).card:ℝ) ≤ a^γ →
      (∀ t ∈ S, τ < ‖Qf t‖ → ‖mrtCofactorPolynomial P F N a t‖ ≤ b) →
      (∑ t ∈ S, ‖Qf t*mrtCofactorPolynomial P F N a t‖^2) ≤
        τ^2*(48000*(2*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T*a/N))+
          b^2*(C/(Real.log a)^2) := by
  obtain ⟨C,γ,hC,hγ,hprime⟩ := sparse_prime_reciprocal_real B hB
  refine ⟨C,γ,hC,hγ,?_⟩
  filter_upwards [hprime] with a haPrime
  intro N P Q F f ha hx hF hf hQ S T τ b hT hτ hsep hdiam hTB Qf hcard hb
  have hsmall := sparse_ramare_cofactor_sampling P F hF N ha hx S hsep hT hdiam
  have hlarge := haPrime Q (S.filter (fun t => τ < ‖Qf t‖)) hQ
    (fun x hx y hy hxy => hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy)
    (fun x hx y hy => (hdiam x (mem_filter.mp hx).1 y (mem_filter.mp hy).1).trans hTB)
    hcard f hf
  apply (mellin_product_sample_split S Qf (mrtCofactorPolynomial P F N a) hτ hb).trans
  exact add_le_add (mul_le_mul_of_nonneg_left hsmall (sq_nonneg _))
    (mul_le_mul_of_nonneg_left hlarge (sq_nonneg _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RamareProductIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the sparse prime/cofactor product estimate -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

/-- The two sample-cardinality premises concern literal finite subsets of
`E`. The prime and cofactor sampling estimates themselves are proved. -/
theorem ramare_product_sparse_integral_jd_oai (B : ℝ) (hB : 1 ≤ B) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ᶠ a : ℝ in atTop, ∀ (N : ℕ) (P Q : Finset ℕ) (F f : ℕ → ℂ),
      1 ≤ a → 2 ≤ (N:ℝ)/a → OneBounded F → OneBounded f →
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ (E : Set ℝ) (T τ b K : ℝ), MeasurableSet E → 0 ≤ T → 0 ≤ τ →
      E ⊆ Set.Ioc (-T) T → 2*T ≤ a^B →
      let Qf := mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ))
      (∀ U : Finset ℝ, (∀ t ∈ U, t ∈ E) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
        (U.card:ℝ) ≤ K ∧ ((U.filter (fun t => τ < ‖Qf t‖)).card:ℝ) ≤ a^γ) →
      (∀ t ∈ E, τ < ‖Qf t‖ → ‖mrtCofactorPolynomial P F N a t‖ ≤ b) →
      (∫ t in E, ‖Qf t*mrtCofactorPolynomial P F N a t‖^2) ≤
        2*(τ^2*(48000*(2*(1+Real.log (2*T+1))+K*Real.sqrt (2*T)*a/N))+
          b^2*(C/(Real.log a)^2)) := by
  obtain ⟨C,γ,hC,hγ,hsample⟩ := ramare_product_sparse_samples B hB
  refine ⟨C,γ,hC,hγ,?_⟩
  filter_upwards [hsample] with a haSample
  intro N P Q F f ha hx hF hf hQ E T τ b K hEm hT hτ hET hTB Qf hcard hb
  apply bounded_integral_le_twice_samples E hEm _
    (((mrtExponentialPolynomial_continuous _ _ _).mul
      (mrtCofactorPolynomial_continuous P F N a)).norm.pow 2)
    (fun _ _ => sq_nonneg _) hT hET
  intro U hUE hsep
  obtain ⟨hK,hγU⟩ := hcard U hUE hsep
  have hdiam : ∀ x ∈ U, ∀ y ∈ U, |x-y| ≤ 2*T := by
    intro x hx y hy
    obtain ⟨hxlo,hxhi⟩ := hET (hUE x hx)
    obtain ⟨hylo,hyhi⟩ := hET (hUE y hy)
    apply abs_le.mpr
    constructor <;> linarith
  have hh := haSample N P Q F f ha hx hF hf hQ U (2*T) τ b
    (by positivity) hτ hsep hdiam hTB hγU
    (fun t ht hqt => hb t (hUE t ht) hqt)
  apply hh.trans
  gcongr

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.ramare_product_sparse_integral_jd_oai := @OAI.JointDickman.ramare_product_sparse_integral_jd_oai
