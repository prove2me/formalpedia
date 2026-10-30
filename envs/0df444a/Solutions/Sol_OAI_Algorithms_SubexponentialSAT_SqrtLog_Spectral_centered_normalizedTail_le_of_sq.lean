-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:41:19.952838+00:00
-- url     : https://prove2.me/submissions/c4506ae3-021c-4a02-8a7d-2ecf8d17ae51

import Mathlib
import Definitions.Def_OAIQ081S014
import Definitions.Def_OAIQ081S020
import Definitions.Def_OAIQ081S021
import Definitions.Def_OAIQ081S022

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSwapMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multiplicities of register-swap eigenvalue labels

The negative local labels are strictly below the diagonal and the positive
labels are on or above it. Counting these labels and their tensor words is
independent of the characteristic of the coefficient field.
-/

namespace SubexponentialSAT.SubexpSwapMultiplicity

open scoped BigOperators

theorem card_negative_eq_sum (r : ℕ) :
    Fintype.card (NegativeLabels r) = ∑ i ∈ Finset.range r, i := by
  rw [Fintype.card_congr
    (Equiv.subtypeProdEquivSigmaSubtype (fun a b : Fin r => b < a)), Fintype.card_sigma]
  have h (a : Fin r) : Fintype.card {b : Fin r // b < a} = a.1 := by
    rw [Fintype.card_of_subtype (Finset.Iio a) (by intro b; simp), Fin.card_Iio]
  simp_rw [h]
  simpa using Fin.sum_univ_eq_sum_range (fun i : ℕ => i) r

theorem card_positive_eq_sum (r : ℕ) :
    Fintype.card (PositiveLabels r) = ∑ i ∈ Finset.range (r + 1), i := by
  rw [Fintype.card_congr (positiveSigmaEquiv r), Fintype.card_sigma]
  have h (b : Fin r) : Fintype.card {a : Fin r // a ≤ b} = b.1 + 1 := by
    rw [Fintype.card_of_subtype (Finset.Iic b) (by intro a; simp), Fin.card_Iic]
  simp_rw [h]
  rw [show (∑ b : Fin r, (b.1 + 1)) = ∑ i ∈ Finset.range r, (i + 1) by
    simpa using Fin.sum_univ_eq_sum_range (fun i : ℕ => i + 1) r]
  simpa using (Finset.sum_range_succ' (fun i : ℕ => i) r).symm

theorem card_negative (r : ℕ) :
    Fintype.card (NegativeLabels r) = r * (r - 1) / 2 := by
  rw [card_negative_eq_sum, Finset.sum_range_id]

theorem card_positive (r : ℕ) :
    Fintype.card (PositiveLabels r) = r * (r + 1) / 2 := by
  rw [card_positive_eq_sum, Finset.sum_range_id]
  simp [Nat.mul_comm]

theorem two_mul_card_negative (r : ℕ) :
    2 * Fintype.card (NegativeLabels r) = r * (r - 1) := by
  rw [card_negative_eq_sum, Nat.mul_comm]
  exact Finset.sum_range_id_mul_two r

theorem two_mul_card_positive (r : ℕ) :
    2 * Fintype.card (PositiveLabels r) = r * (r + 1) := by
  rw [card_positive_eq_sum, Nat.mul_comm]
  simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two (r + 1)

theorem positiveMultiplicity_cast (r : ℕ) :
    (positiveMultiplicity r : ℚ) = (r : ℚ) * (r + 1) / 2 := by
  have h := congrArg (fun n : ℕ => (n : ℚ)) (two_mul_card_positive r)
  rw [card_positive] at h
  change ((2 * positiveMultiplicity r : ℕ) : ℚ) = ((r * (r + 1) : ℕ) : ℚ) at h
  push_cast at h
  linarith

theorem negativeMultiplicity_cast (r : ℕ) (hr : 0 < r) :
    (negativeMultiplicity r : ℚ) = (r : ℚ) * (r - 1) / 2 := by
  have h := congrArg (fun n : ℕ => (n : ℚ)) (two_mul_card_negative r)
  rw [card_negative] at h
  change ((2 * negativeMultiplicity r : ℕ) : ℚ) = ((r * (r - 1) : ℕ) : ℚ) at h
  have hr1 : 1 ≤ r := hr
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hr1, Nat.cast_one] at h
  linarith

theorem negativeMultiplicity_ratio (r : ℕ) (hr : 0 < r) :
    (negativeMultiplicity r : ℚ) / (r : ℚ) ^ 2 = negativeProbability r := by
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  rw [negativeMultiplicity_cast r hr, negativeProbability]
  field_simp

theorem positiveMultiplicity_ratio (r : ℕ) (hr : 0 < r) :
    (positiveMultiplicity r : ℚ) / (r : ℚ) ^ 2 = 1 - negativeProbability r := by
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  rw [positiveMultiplicity_cast, negativeProbability]
  field_simp
  ring

/-- Exact binomial probability mass function of the negative weight. -/
theorem swapProbability_eq_binomial (r q w : ℕ) (hr : 0 < r) :
    swapProbability r q w =
      (q.choose w : ℚ) * negativeProbability r ^ w *
        (1 - negativeProbability r) ^ (q - w) := by
  by_cases hw : w ≤ q
  · unfold swapProbability swapMultiplicity
    push_cast
    calc
      _ = (q.choose w : ℚ) *
          (((positiveMultiplicity r : ℚ) / (r : ℚ) ^ 2) ^ (q - w) *
            ((negativeMultiplicity r : ℚ) / (r : ℚ) ^ 2) ^ w) := by
        rw [div_pow, div_pow, ← mul_div_mul_comm, ← pow_add, Nat.sub_add_cancel hw]
        ring
      _ = _ := by
        rw [positiveMultiplicity_ratio r hr, negativeMultiplicity_ratio r hr]
        ring
  · have hz : q.choose w = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hw)
    simp [swapProbability, swapMultiplicity, hz]

/-- The local negative probability belongs to the range used in the paper. -/
theorem negativeProbability_bounds (r : ℕ) (hr : 2 ≤ r) :
    (1 / 4 : ℚ) ≤ negativeProbability r ∧ negativeProbability r < 1 / 2 := by
  have hrQ : (2 : ℚ) ≤ r := by exact_mod_cast hr
  have hden : (0 : ℚ) < 2 * r := by linarith
  constructor
  · unfold negativeProbability
    apply (le_div_iff₀ hden).mpr
    linarith
  · unfold negativeProbability
    apply (div_lt_iff₀ hden).mpr
    linarith

/-! ## General binomial second moment and the interval tail -/

end SubexponentialSAT.SubexpSwapMultiplicity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SpectralBinomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exponential concentration for the exact binomial swap spectrum.
All distribution parameters are explicit; no arity parameter is fixed. -/

namespace SubexponentialSAT.SqrtLog.Spectral

open scoped BigOperators

theorem binomialMean_succ (θ : ℝ) (q : ℕ) (f : ℕ → ℝ) :
    binomialMean θ (q + 1) f =
      binomialMean θ q (fun w => (1 - θ) * f w + θ * f (w + 1)) := by
  unfold binomialMean
  simp only [mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun i j => (1 - θ) ^ j * (θ ^ i * f i)) q]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  have hwle : w ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hw)
  have he : q + 1 - w = q - w + 1 := by omega
  rw [he, pow_succ, pow_succ]
  ring

theorem binomialMean_const_mul (θ c : ℝ) (q : ℕ) (f : ℕ → ℝ) :
    binomialMean θ q (fun w => c * f w) = c * binomialMean θ q f := by
  simp [binomialMean, mul_left_comm, ← Finset.mul_sum]

theorem binomialMean_add (θ : ℝ) (q : ℕ) (f g : ℕ → ℝ) :
    binomialMean θ q (fun w => f w + g w) =
      binomialMean θ q f + binomialMean θ q g := by
  simp [binomialMean, mul_add, Finset.sum_add_distrib]

theorem bernoulli_mgf_le (θ t : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ)) ≤
      Real.exp (t ^ 2 / 2) := by
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hj := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-t))
    (show 0 ≤ 1 - θ by linarith) hθ0 (show 1 - θ + θ = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hj
  have hj' : Real.exp (-t * θ) ≤ 1 - θ + θ * Real.exp (-t) := by
    simpa only [mul_neg, mul_comm] using hj
  have hb : 0 ≤ 1 - θ + θ * Real.exp t := by positivity
  have hm := mul_le_mul_of_nonneg_left hj' hb
  have he : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hexp : Real.exp (t * (1 - θ)) = Real.exp t * Real.exp (-t * θ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfirst : (1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ)) ≤
      1 + 2 * θ * (1 - θ) * (Real.cosh t - 1) := by
    rw [hexp]
    calc
      _ = (1 - θ + θ * Real.exp t) * Real.exp (-t * θ) := by ring
      _ ≤ (1 - θ + θ * Real.exp t) * (1 - θ + θ * Real.exp (-t)) := hm
      _ = _ := by
        rw [Real.cosh_eq]
        linear_combination θ ^ 2 * he
  have hc : 0 ≤ Real.cosh t - 1 := sub_nonneg.mpr (Real.one_le_cosh t)
  have hv : 2 * θ * (1 - θ) ≤ 1 := by nlinarith [sq_nonneg (θ - 1 / 2)]
  have hsecond : 1 + 2 * θ * (1 - θ) * (Real.cosh t - 1) ≤ Real.cosh t := by
    nlinarith [mul_le_mul_of_nonneg_right hv hc]
  exact hfirst.trans (hsecond.trans (Real.cosh_le_exp_half_sq t))

theorem binomial_mgf_le (θ t : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (q : ℕ) :
    binomialMean θ q (fun w => Real.exp (t * ((w : ℝ) - q * θ))) ≤
      Real.exp ((q : ℝ) * t ^ 2 / 2) := by
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  induction q with
  | zero => simp [binomialMean]
  | succ q ih =>
    rw [binomialMean_succ]
    have hfun :
        (fun w : ℕ => (1 - θ) * Real.exp (t * ((w : ℝ) - (q + 1 : ℕ) * θ)) +
          θ * Real.exp (t * ((w + 1 : ℕ) - (q + 1 : ℕ) * θ))) =
        (fun w : ℕ => ((1 - θ) * Real.exp (-t * θ) +
          θ * Real.exp (t * (1 - θ))) * Real.exp (t * ((w : ℝ) - q * θ))) := by
      funext w
      have h0 : t * ((w : ℝ) - (q + 1 : ℕ) * θ) =
          -t * θ + t * ((w : ℝ) - q * θ) := by push_cast; ring
      have h1 : t * ((w + 1 : ℕ) - (q + 1 : ℕ) * θ) =
          t * (1 - θ) + t * ((w : ℝ) - q * θ) := by push_cast; ring
      rw [h0, h1, Real.exp_add, Real.exp_add]
      ring
    rw [hfun, binomialMean_const_mul]
    have hfac : 0 ≤ (1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ)) := by
      positivity
    calc
      _ ≤ ((1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ))) *
          Real.exp ((q : ℝ) * t ^ 2 / 2) := mul_le_mul_of_nonneg_left ih hfac
      _ ≤ Real.exp (t ^ 2 / 2) * Real.exp ((q : ℝ) * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (bernoulli_mgf_le θ t hθ0 hθ1) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

theorem binomialMean_mono (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (q : ℕ) (f g : ℕ → ℝ) (hfg : ∀ w ∈ Finset.range (q + 1), f w ≤ g w) :
    binomialMean θ q f ≤ binomialMean θ q g := by
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  apply Finset.sum_le_sum
  intro w hw
  exact mul_le_mul_of_nonneg_left (hfg w hw) (by positivity)

/-- Two-sided finite-binomial concentration with an absolute constant.
The event may be any finite predicate separated from the exact mean. -/
theorem binomial_tail_le (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (q : ℕ) (hq : 0 < q) (b : ℝ) (hb : 0 ≤ b)
    (bad : ℕ → Prop) [DecidablePred bad]
    (hbad : ∀ w ∈ Finset.range (q + 1), bad w → b ≤ |(w : ℝ) - q * θ|) :
    binomialMean θ q (fun w => if bad w then 1 else 0) ≤
      2 * Real.exp (-(b ^ 2) / (2 * q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let t : ℝ := b / q
  have ht : 0 ≤ t := div_nonneg hb hqR.le
  have hpoint : ∀ w ∈ Finset.range (q + 1),
      (if bad w then (1 : ℝ) else 0) ≤
        Real.exp (t * (((w : ℝ) - q * θ) - b)) +
        Real.exp (t * (-((w : ℝ) - q * θ) - b)) := by
    intro w hw
    split_ifs with h
    · rcases le_abs.mp (hbad w hw h) with hp | hn
      · have he : 1 ≤ Real.exp (t * (((w : ℝ) - q * θ) - b)) :=
          Real.one_le_exp_iff.mpr (mul_nonneg ht (sub_nonneg.mpr hp))
        linarith [Real.exp_pos (t * (-((w : ℝ) - q * θ) - b))]
      · have he : 1 ≤ Real.exp (t * (-((w : ℝ) - q * θ) - b)) :=
          Real.one_le_exp_iff.mpr (mul_nonneg ht (sub_nonneg.mpr hn))
        linarith [Real.exp_pos (t * (((w : ℝ) - q * θ) - b))]
    · positivity
  have hbound := binomialMean_mono θ hθ0 hθ1 q _ _ hpoint
  have hfun :
      (fun w : ℕ => Real.exp (t * (((w : ℝ) - q * θ) - b)) +
        Real.exp (t * (-((w : ℝ) - q * θ) - b))) =
      (fun w : ℕ => Real.exp (-t * b) *
        (Real.exp (t * ((w : ℝ) - q * θ)) +
         Real.exp ((-t) * ((w : ℝ) - q * θ)))) := by
    funext w
    have h1 : t * (((w : ℝ) - q * θ) - b) = -t * b + t * ((w : ℝ) - q * θ) := by ring
    have h2 : t * (-((w : ℝ) - q * θ) - b) = -t * b + (-t) * ((w : ℝ) - q * θ) := by ring
    rw [h1, h2, Real.exp_add, Real.exp_add]
    ring
  rw [hfun, binomialMean_const_mul, binomialMean_add] at hbound
  have hp := binomial_mgf_le θ t hθ0 hθ1 q
  have hn := binomial_mgf_le θ (-t) hθ0 hθ1 q
  rw [neg_sq] at hn
  calc
    _ ≤ Real.exp (-t * b) *
        (binomialMean θ q (fun w => Real.exp (t * ((w : ℝ) - q * θ))) +
         binomialMean θ q (fun w => Real.exp ((-t) * ((w : ℝ) - q * θ)))) := hbound
    _ ≤ Real.exp (-t * b) * (2 * Real.exp ((q : ℝ) * t ^ 2 / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith
    _ = 2 * Real.exp (-(b ^ 2) / (2 * q)) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      dsimp [t]
      field_simp
      ; ring

end SubexponentialSAT.SqrtLog.Spectral

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SpectralRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual rank bounds for the multi-color swap construction

The linear-algebra input is the dimension of the actual range of `id - M`.
The local swap multiplicities and the finite tail are kept as ordinary natural
counts, and converted to real inequalities only at the final scaling step.
-/

namespace SubexponentialSAT.Subexp.SpectralRank

open Module
open scoped BigOperators

section ProbabilityTail

open SubexponentialSAT.Subexp.TensorSpectrum SubexponentialSAT.SubexpSwapMultiplicity

/-- The probability tail is exactly the source's binomial tail with negative
probability `(r - 1) / (2*r)`. -/
theorem normalizedTail_eq_binomial (r q A R : ℕ) (hr : 0 < r) :
    normalizedTail r q A R =
      ∑ w ∈ Finset.range (q + 1), if w ∈ Finset.Ico A (A + R) then 0 else
        (q.choose w : ℚ) * negativeProbability r ^ w *
          (1 - negativeProbability r) ^ (q - w) := by
  simp only [normalizedTail, swapProbability_eq_binomial r q _ hr]

end ProbabilityTail

end SubexponentialSAT.Subexp.SpectralRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TailInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A computable centered interval for the multicolor binomial tail

The swap mean is between (Q - 1) / 4 and (Q - 1) / 2.  Taking the natural
floor of mean - R / 2 gives an interval of R consecutive integer weights.
The rounding error is at most one, absorbed by R ≥ 4.
-/

namespace SubexponentialSAT.Subexp.TailInterval

open SubexponentialSAT.SubexpSwapMultiplicity
open scoped BigOperators

theorem centeredStart_bounds {μ : ℚ} {R : ℕ} (hcenter : (R : ℚ) / 2 ≤ μ) :
    (centeredStart μ R : ℚ) ≤ μ - (R : ℚ) / 2 ∧
      μ - (R : ℚ) / 2 < (centeredStart μ R : ℚ) + 1 := by
  exact ⟨Nat.floor_le (by linarith), Nat.lt_floor_add_one _⟩

/-- The floor rounding error preserves distance at least R / 4 outside
the interval.  This holds for every natural weight, not just weights ≤ Q - 1. -/
theorem centeredStart_deviation {μ : ℚ} {R w : ℕ}
    (hR : 4 ≤ R) (hcenter : (R : ℚ) / 2 ≤ μ)
    (hw : w ∉ Finset.Ico (centeredStart μ R) (centeredStart μ R + R)) :
    (R : ℚ) ^ 2 ≤ 16 * ((w : ℚ) - μ) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := centeredStart_bounds hcenter
  have hR0 : (0 : ℚ) ≤ R := Nat.cast_nonneg _
  have hR4 : (4 : ℚ) ≤ R := by exact_mod_cast hR
  by_cases hleft : w < centeredStart μ R
  · have hwQ : (w : ℚ) < centeredStart μ R := by exact_mod_cast hleft
    have hdist : (R : ℚ) ≤ 4 * (μ - w) := by linarith
    have hs := mul_self_le_mul_self hR0 hdist
    nlinarith
  · have hright : centeredStart μ R + R ≤ w := by
      simp only [Finset.mem_Ico] at hw
      omega
    have hwQ : (centeredStart μ R : ℚ) + R ≤ w := by exact_mod_cast hright
    have hdist : (R : ℚ) ≤ 4 * (w - μ) := by linarith
    have hs := mul_self_le_mul_self hR0 hdist
    nlinarith

theorem mean_bounds (r Q : ℕ) (hr : 2 ≤ r) :
    ((Q - 1 : ℕ) : ℚ) / 4 ≤ mean r Q ∧
      mean r Q ≤ ((Q - 1 : ℕ) : ℚ) / 2 := by
  obtain ⟨hlo, hhi⟩ := negativeProbability_bounds r hr
  have hlo' := mul_le_mul_of_nonneg_left hlo (show (0 : ℚ) ≤ (Q - 1 : ℕ) from Nat.cast_nonneg _)
  have hhi' := mul_le_mul_of_nonneg_left hhi.le (show (0 : ℚ) ≤ (Q - 1 : ℕ) from Nat.cast_nonneg _)
  dsimp [mean]
  constructor <;> linarith

theorem half_width_le_mean {r Q R : ℕ} (hr : 2 ≤ r)
    (hsize : 4 * R ≤ Q) :
    (R : ℚ) / 2 ≤ mean r Q := by
  have hq : 2 * R ≤ Q - 1 := by omega
  have hqQ : (2 : ℚ) * R ≤ (Q - 1 : ℕ) := by exact_mod_cast hq
  have hlo := (mean_bounds r Q hr).1
  linarith

/-- Required geometric hypothesis for the exact swap-probability tail bound. -/
theorem intervalStart_deviation {r Q R w : ℕ} (hr : 2 ≤ r)
    (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hw : w ∉ Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R)) :
    (R : ℚ) ^ 2 ≤
      16 * ((w : ℚ) - (Q - 1 : ℕ) * negativeProbability r) ^ 2 :=
  centeredStart_deviation hR (half_width_le_mean hr hsize) hw

end SubexponentialSAT.Subexp.TailInterval

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SpectralTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Centered integer windows for the actual swap spectrum. The original
rational-floor interval is reused, so the numerical constant is deliberately
loose while the square-root/logarithmic dependence is retained. -/

namespace SubexponentialSAT.SqrtLog.Spectral

open scoped BigOperators
open SubexponentialSAT.SubexpSwapMultiplicity SubexponentialSAT.Subexp.SpectralRank

theorem normalizedTail_cast (r q A R : ℕ) (hr : 0 < r) :
    (normalizedTail r q A R : ℝ) =
      binomialMean (negativeProbability r : ℝ) q
        (fun w => if w ∉ Finset.Ico A (A + R) then 1 else 0) := by
  rw [normalizedTail_eq_binomial r q A R hr]
  unfold binomialMean
  push_cast
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hin : w ∈ Finset.Ico A (A + R)
  · simp [hin]
  · simp only [hin, not_false_eq_true, ite_true, if_true, ite_false, mul_one]
    push_cast
    ring

/-- Explicit exponential estimate for the already implemented interval.
The statement is uniform in all colors and every future layout arity. -/
theorem centered_normalizedTail_le_exp {r Q R : ℕ}
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q) :
    (normalizedTail r (Q - 1) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R : ℝ) ≤
      2 * Real.exp (-((R : ℝ) ^ 2) / (32 * (Q - 1 : ℕ))) := by
  rw [normalizedTail_cast r (Q - 1) _ R (by omega)]
  have hprob := negativeProbability_bounds r hr
  have hθ0 : (0 : ℝ) ≤ (negativeProbability r : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ negativeProbability r by linarith [hprob.1])
  have hθ1 : (negativeProbability r : ℝ) ≤ 1 := by
    exact_mod_cast (show negativeProbability r ≤ (1 : ℚ) by linarith [hprob.2])
  have ht := binomial_tail_le (negativeProbability r : ℝ) hθ0 hθ1
    (Q - 1) (by omega) ((R : ℝ) / 4) (by positivity)
    (fun w => w ∉ Finset.Ico (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R)
      (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R + R)) (by
        intro w _ hw
        have hs := SubexponentialSAT.Subexp.TailInterval.intervalStart_deviation hr hR hsize hw
        have hsR : (R : ℝ) ^ 2 ≤ 16 *
            ((w : ℝ) - (Q - 1 : ℕ) * (negativeProbability r : ℝ)) ^ 2 := by
          exact_mod_cast hs
        have ha := abs_nonneg ((w : ℝ) - (Q - 1 : ℕ) * (negativeProbability r : ℝ))
        have he := sq_abs ((w : ℝ) - (Q - 1 : ℕ) * (negativeProbability r : ℝ))
        have hRp : (0 : ℝ) ≤ R := Nat.cast_nonneg R
        nlinarith)
  convert ht using 1 ; congr 2 ; ring

/-- A rational tail budget for the concrete interval, ready for the
audited rank theorem. This is an explicit numerical sufficient condition. -/
theorem centered_normalizedTail_le {r Q R : ℕ} (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hbudget : 2 * Real.exp (-((R : ℝ) ^ 2) / (32 * (Q - 1 : ℕ))) ≤ (ε : ℝ)) :
    normalizedTail r (Q - 1) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R ≤ ε := by
  have ht := (centered_normalizedTail_le_exp hr hQ hR hsize).trans hbudget
  exact_mod_cast ht

/-- A logarithmic square-width test discharges the exponential budget. -/
theorem exp_budget_of_sq {q R : ℕ} (hq : 0 < q) {ε : ℝ} (hε : 0 < ε)
    (hwidth : 32 * (q : ℝ) * Real.log (2 / ε) ≤ (R : ℝ) ^ 2) :
    2 * Real.exp (-((R : ℝ) ^ 2) / (32 * q)) ≤ ε := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hden : (0 : ℝ) < 32 * q := by positivity
  have hx : -((R : ℝ) ^ 2) / (32 * q) ≤ -Real.log (2 / ε) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have he := Real.exp_le_exp.mpr hx
  have hlog : Real.exp (-Real.log (2 / ε)) = ε / 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hlog] at he
  linarith

theorem centered_normalizedTail_le_of_sq_oai {r Q R : ℕ} (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    normalizedTail r (Q - 1) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R ≤ ε := by
  apply centered_normalizedTail_le ε hr hQ hR hsize
  exact exp_budget_of_sq (by omega) (by exact_mod_cast hε) hwidth

end SubexponentialSAT.SqrtLog.Spectral

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq_oai
