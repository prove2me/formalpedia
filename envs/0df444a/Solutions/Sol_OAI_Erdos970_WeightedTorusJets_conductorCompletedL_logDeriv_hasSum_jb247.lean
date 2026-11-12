-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.conductorCompletedL_logDeriv_hasSum_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:49:51.780017+00:00
-- url     : https://prove2.me/submissions/d5ccd0cc-5849-4da8-b3bd-7aeb19f51b3c

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J000
import Definitions.Def_OAIQ247J005
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_conductorCompletedL_hadamard_factorization_jb247

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_SpecialFunctions_Complex_LogBounds
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Logarithm estimates for Weierstrass products

This file develops the finite truncation and tail estimates for the logarithm series
`-log (1 - z)`.  These estimates are the local analytic input for bounding Weierstrass
factors and canonical products.
-/


open scoped BigOperators

namespace Real

/-- If `0 ≤ r ≤ 1 / 2`, then the geometric-factor denominator is bounded by `2`. -/
lemma pow_div_one_sub_le_two_mul {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (m : ℕ) :
    r ^ (m + 1) / (1 - r) ≤ 2 * r ^ (m + 1) := by
  have hpow : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hhalf' : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  calc
    r ^ (m + 1) / (1 - r) ≤ r ^ (m + 1) / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left hpow (by positivity) hhalf'
    _ = 2 * r ^ (m + 1) := by ring

end Real

namespace Complex

open scoped BigOperators in
/-- On the open unit disk, `-log (1 - z)` is the `tsum` with index shift `n ↦ n + 1`. -/
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]

lemma logTaylor_succ_neg (n : ℕ) (z : ℂ) :
    logTaylor (n + 1) (-z) = logTaylor n (-z) - z ^ n / n := by
  rw [logTaylor_succ, Pi.add_apply]
  have hsign : (-1 : ℂ) ^ (n + 1) * (-z) ^ n = -z ^ n := by
    have hzpow : (-z) ^ n = (((-1 : ℂ) * z) ^ n) := by simp
    rw [hzpow, mul_pow, ← mul_assoc, ← pow_add]
    have hpow : (-1 : ℂ) ^ (n + 1 + n) = (-1 : ℂ) := by
      rw [show n + 1 + n = 2 * n + 1 by omega, pow_add, pow_mul]
      norm_num
    rw [hpow]
    ring
  rw [show (-1 : ℂ) ^ (n + 1) * (-z) ^ n / n = -(z ^ n / n) by
    rw [hsign]
    ring]
  abel

/-- Evaluate `logTaylor` at `-z` as a finite positive-coefficient logarithm sum. -/
lemma logTaylor_neg_eq_neg_sum (m : ℕ) (z : ℂ) :
    logTaylor (m + 1) (-z) = -∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  induction m with
  | zero =>
      simp [logTaylor_succ, logTaylor_zero]
  | succ m hm =>
      rw [logTaylor_succ_neg, hm, Finset.sum_range_succ]
      have hcast : ((m + 1 : ℕ) : ℂ) = (1 + (m : ℂ)) := by
        simp [Nat.cast_add, Nat.cast_one, add_comm]
      rw [hcast]
      ring_nf

/-- `partialLogSum` is the partial sum `∑_{k=1}^m z^k / k`. -/
lemma partialLogSum_eq_sum (m : ℕ) (z : ℂ) :
    partialLogSum m z = ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  simpa [partialLogSum] using congrArg Neg.neg (logTaylor_neg_eq_neg_sum m z)

lemma hasDerivAt_partialLogSum (m : ℕ) (z : ℂ) :
    HasDerivAt (partialLogSum m) (∑ j ∈ Finset.range m, z ^ j) z := by
  cases m with
  | zero =>
      have hzero : partialLogSum 0 = fun _ : ℂ ↦ (0 : ℂ) := by
        funext w
        exact partialLogSum_zero w
      simpa [hzero] using (hasDerivAt_const z (c := (0 : ℂ)))
  | succ m =>
      have hsum :
          (∑ j ∈ Finset.range (m + 1), z ^ j) =
            ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (-z) ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        calc
          (-1 : ℂ) ^ j * (-z) ^ j = (-1 : ℂ) ^ j * (((-1 : ℂ) * z) ^ j) := by simp
          _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * z ^ j := by rw [mul_pow]; ring
          _ = z ^ j := by
                rw [← pow_add, show j + j = 2 * j by omega, pow_mul]
                norm_num
      rw [hsum]
      simpa [partialLogSum] using!
        (((hasDerivAt_logTaylor (m + 1) (-z)).comp z (hasDerivAt_neg z)).neg)

lemma differentiable_partialLogSum (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => partialLogSum m z) := by
  intro z
  exact (hasDerivAt_partialLogSum m z).differentiableAt

lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom ?_
  intro k
  rw [norm_div, norm_pow]
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Complex.norm_natCast (m + 1 + k))
  rw [hnorm]
  calc
    ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ) ≤ ‖z‖ ^ (m + 1 + k) := by
      exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _

/-- A coarse geometric-series bound for the logarithm tail. This intentionally drops the
extra denominator `m + 1 + k`; the weaker estimate is the form used by the Weierstrass-factor
bounds below. -/
lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  dsimp only [logTail]
  have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
  have h_norm_summable : Summable (fun k => ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_rhs_summable
    intro k
    rw [norm_div, norm_pow]
    have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (m + 1 + k))
    rw [hnorm]
    have hm : 1 ≤ (m + 1 + k : ℝ) := by
      have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
      nlinarith
    exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ :=
          norm_tsum_le_tsum_norm h_norm_summable
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          refine h_norm_summable.tsum_le_tsum ?_ h_rhs_summable
          intro k
          rw [norm_div, norm_pow]
          have hm : 1 ≤ (m + 1 + k : ℝ) := by
            have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
            nlinarith
          have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (m + 1 + k))
          rw [hnorm]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq :
              (fun k => ‖z‖ ^ (m + 1 + k)) = fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by
            ext k
            rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [h_geom.tsum_eq, div_eq_mul_inv]

lemma norm_logTail_le_two_mul_norm_pow {z : ℂ} (hz : ‖z‖ < 1) (hzhalf : ‖z‖ ≤ 1 / 2) (m : ℕ) :
    ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
  (norm_logTail_le hz m).trans (Real.pow_div_one_sub_le_two_mul (norm_nonneg z) hzhalf m)

/-- Decompose the logarithm series into its first `m` terms and the remaining tail. -/
lemma neg_log_one_sub_eq_partialLogSum_add_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    -log (1 - z) = partialLogSum m z + logTail m z := by
  let f : ℕ → ℂ := fun k ↦ z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (summable_logTail hz 0)
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  rw [neg_log_one_sub_eq_tsum hz, partialLogSum_eq_sum, ← h_decomp]
  congr 1
  dsimp only [logTail]
  refine tsum_congr fun k ↦ ?_
  simp only [f, Nat.cast_add]
  ring_nf

end Complex
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_WeierstrassFactor
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Complex.canonicalProduct_def _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem _root_.Erdos970.Complex.Hadamard.divisorComplementPartialProduct_def _root_.Erdos970.Complex.Hadamard.divisorPartialProduct_def _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Weierstrass elementary factors

We define the Weierstrass elementary factors
`E_m(z) = (1 - z) * exp (∑_{k=1}^m z^k / k)` (as `Complex.weierstrassFactor`) and prove basic
properties and estimates

## Main definitions

* `Complex.partialLogSum m z`: the truncation of `-log (1 - z)`, defined via `Complex.logTaylor`
* `Complex.logTail m z`: the tail `∑_{k>m} z^k / k` as a `tsum` starting at `m + 1`
* `Complex.weierstrassFactor m z`: the elementary factor `E_m(z)`

## Main results

* `Complex.weierstrassFactor_sub_one_pow_bound`: `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)` for `‖z‖ ≤ 1 / 2`
* `Complex.weierstrassFactor_eq_exp_neg_tail`: on `‖z‖ < 1` with `z ≠ 1`,
  `E_m z = exp (-logTail m z)`
* `Complex.norm_partialLogSum_le_nat_mul_max_one_norm_pow`: a crude bound on the truncated
  logarithm series
* `Complex.log_norm_weierstrassFactor_ge_log_norm_one_sub_nat_mul_max_one_norm_pow`: a crude lower
  bound for `log ‖E_m(z)‖` used in minimum-modulus arguments
-/


noncomputable section

open scoped BigOperators
open Set

namespace Complex

/-! ## The Weierstrass factor -/

lemma weierstrassFactor_def (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = (1 - z) * exp (partialLogSum m z) := by
  simp [weierstrassFactor]

lemma weierstrassFactor_eq_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = 0 ↔ z = 1 := by
  constructor
  · intro hz
    rw [weierstrassFactor] at hz
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact (sub_eq_zero.mp h1).symm
    · exact absurd h2 (exp_ne_zero _)
  · rintro rfl
    simp [weierstrassFactor]

lemma weierstrassFactor_ne_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z ≠ 0 ↔ z ≠ 1 := by
  simpa [ne_eq] using (not_congr (weierstrassFactor_eq_zero_iff (m := m) (z := z)))

lemma weierstrassFactor_ne_zero_of_ne_one (m : ℕ) {z : ℂ} (hz : z ≠ 1) :
    weierstrassFactor m z ≠ 0 :=
  (weierstrassFactor_ne_zero_iff (m := m) (z := z)).2 hz

lemma differentiable_weierstrassFactor (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m z) := by
  simpa [weierstrassFactor] using!
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
      (differentiable_exp.comp (differentiable_partialLogSum m))

/-- The elementary factor `z ↦ E_m (z / a)` has a simple zero at `a`. -/
theorem analyticOrderAt_weierstrassFactor_div_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderAt (fun z : ℂ => weierstrassFactor m (z / a)) a = (1 : ℕ∞) := by
  set F : ℂ → ℂ := fun z => weierstrassFactor m (z / a)
  have hF : AnalyticAt ℂ F a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hdiff : Differentiable ℂ F := (differentiable_weierstrassFactor m).comp hdiv
    exact Differentiable.analyticAt (f := F) hdiff a
  let g : ℂ → ℂ := fun z => (-a⁻¹) * Complex.exp (partialLogSum m (z / a))
  have hg : AnalyticAt ℂ g a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hpls : Differentiable ℂ (fun z : ℂ => partialLogSum m (z / a)) :=
      (differentiable_partialLogSum m).comp hdiv
    have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (partialLogSum m (z / a))) :=
      (Complex.differentiable_exp).comp hpls
    have hdiffg : Differentiable ℂ g := by
      simpa [g] using hexp.const_mul (-a⁻¹ : ℂ)
    exact Differentiable.analyticAt (f := g) hdiffg a
  have hg0 : g a ≠ 0 := by
    have hconst : (-a⁻¹ : ℂ) ≠ 0 := by simp [ha]
    have hexp0 : Complex.exp (partialLogSum m (a / a)) ≠ 0 :=
      Complex.exp_ne_zero (partialLogSum m (a / a))
    simpa [g] using mul_ne_zero hconst hexp0
  refine (hF.analyticOrderAt_eq_natCast (n := 1)).2 ?_
  refine ⟨g, hg, hg0, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro z
  have hlin : (1 - z / a) = (z - a) * (-a⁻¹) := by
    have h1 : (1 : ℂ) = a * a⁻¹ := by simp [ha]
    simp [div_eq_mul_inv, h1]
    ring
  simp only [F, g, pow_one, smul_eq_mul]
  rw [weierstrassFactor_def]
  simp [hlin, mul_assoc]

/-- For `‖z‖ < 1` and `z ≠ 1`, `E_m(z) = exp(-logTail_m(z))`. -/
lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + partialLogSum m z = -logTail m z := by
    have hdecomp := neg_log_one_sub_eq_partialLogSum_add_logTail hz m
    calc
      log (1 - z) + partialLogSum m z
          = log (1 - z) + (partialLogSum m z + logTail m z) - logTail m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - logTail m z := by rw [hdecomp]
      _ = -logTail m z := by ring
  simp [hsum]

/-! ## Power bound -/

/-- For `‖z‖ ≤ 1 / 2`, `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)`. -/
theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [weierstrassFactor] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    have h_tail_bound := norm_logTail_le_two_mul_norm_pow hz_lt hz m
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖logTail m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (h_tail_bound.trans hmul).trans hsq
      linarith
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring

/-!
## Lower bounds on `Real.log ‖weierstrassFactor m z‖`

Auxiliary inequalities for minimum-modulus / Cartan-type arguments in Hadamard factorization.
-/

/-! ## Locally uniform convergence of products of scaled factors -/

end Complex
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_CanonicalProduct
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem _root_.Erdos970.Complex.Hadamard.divisorComplementPartialProduct_def _root_.Erdos970.Complex.Hadamard.divisorPartialProduct_def _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Canonical products

This file defines canonical products attached to a sequence `a : ℕ → ℂ`:

`canonicalProduct m a z := ∏' n, weierstrassFactor m (z / a n)`.

The convergence results specialize the locally uniform product API for scaled Weierstrass factors
developed in `Mathlib.Analysis.Complex.WeierstrassFactor`.
-/


noncomputable section

open Filter Topology

namespace Complex

/-- Genus-one Weierstrass factors contribute the usual `1 / (z - a) + 1 / a` term to
the logarithmic derivative. -/
theorem logDeriv_weierstrassFactor_one_div {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ a) :
    logDeriv (fun w : ℂ => weierstrassFactor 1 (w / a)) z =
      1 / (z - a) + 1 / a := by
  have hE :
      (fun w : ℂ => weierstrassFactor 1 (w / a)) =
        fun w : ℂ => (1 - w / a) * exp (w / a) := by
    ext w
    simp [weierstrassFactor_def, partialLogSum_eq_sum]
  have hf : (1 - z / a) ≠ 0 := by
    intro hzero
    have hdiv : z / a = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    exact hz ((div_eq_one_iff_eq ha).1 hdiv)
  rw [hE, logDeriv_mul (f := fun w : ℂ => 1 - w / a) (g := fun w : ℂ => exp (w / a))
    z hf (exp_ne_zero (z / a)) (by fun_prop) (by fun_prop)]
  have hleft : logDeriv (fun w : ℂ => 1 - w / a) z = 1 / (z - a) := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => 1 - w / a) z = -(1 / a) := by
      simp [one_div]
    rw [hderiv]
    have haz : -z + a ≠ 0 := by
      simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr (Ne.symm hz)
    field_simp [ha, sub_ne_zero.mpr hz, haz]
    have haz' : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have hza : z - a = -(a - z) := by ring
    rw [hza]
    field_simp [haz']
  have hright : logDeriv (fun w : ℂ => exp (w / a)) z = 1 / a := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => exp (w / a)) z =
        exp (z / a) * (1 / a) := by
      simp [one_div]
    rw [hderiv]
    field_simp [exp_ne_zero (z / a)]
  rw [hleft, hright]

end Complex
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_LocallyUniformLimit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Locally uniform limits and bounded multiplication

Uniform convergence on a set is preserved under multiplication by a function that is bounded
on that set.  This is a basic estimate for locally uniform products.
-/


namespace Complex

section UniformMul

/-- On `K`, uniform convergence is preserved when multiplying on the left by a bounded function. -/
theorem _root_.TendstoUniformlyOn.mul_left_bounded {ι : Type*} {p : Filter ι} {K : Set ℂ}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {h : ℂ → ℂ}
    (hF : TendstoUniformlyOn F f p K) (hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C) :
    TendstoUniformlyOn (fun n z => h z * F n z) (fun z => h z * f z) p K := by
  intro u hu
  rcases Metric.mem_uniformity_dist.1 hu with ⟨ε, hεpos, hεu⟩
  rcases hh with ⟨C, hC⟩
  set C' : ℝ := max C 1
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hC' : ∀ z ∈ K, ‖h z‖ ≤ C' := fun z hz => le_trans (hC z hz) (le_max_left _ _)
  have hv : {p : ℂ × ℂ | dist p.1 p.2 < ε / C'} ∈ uniformity ℂ :=
    Metric.mem_uniformity_dist.2 ⟨ε / C', div_pos hεpos hC'pos, fun _ _ hab => hab⟩
  have hF' : ∀ᶠ n in p, ∀ z : ℂ, z ∈ K → dist (f z) (F n z) < ε / C' := hF _ hv
  filter_upwards [hF'] with n hn z hzK
  have hn' : ‖f z - F n z‖ < ε / C' := by simpa [dist_eq_norm] using hn z hzK
  have hle : ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ :=
    mul_le_mul_of_nonneg_right (hC' z hzK) (norm_nonneg _)
  have hlt : C' * ‖f z - F n z‖ < C' * (ε / C') := mul_lt_mul_of_pos_left hn' hC'pos
  have hnorm :
      ‖h z * f z - h z * F n z‖ = ‖h z‖ * ‖f z - F n z‖ := by
    calc
      ‖h z * f z - h z * F n z‖ = ‖h z * (f z - F n z)‖ := by simp [mul_sub]
      _ = ‖h z‖ * ‖f z - F n z‖ := by simp
  have hdist : dist (h z * f z) (h z * F n z) < ε := by
    rw [dist_eq_norm, hnorm]
    have hlt' : ‖h z‖ * ‖f z - F n z‖ < ε := by
      calc
        ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ := hle
        _ < C' * (ε / C') := hlt
        _ = ε := by field_simp [hC'pos.ne']
    exact hlt'
  exact hεu hdist

end UniformMul

end Complex
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_DivisorConvergence
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_one_of_mem _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem _root_.Erdos970.Complex.Hadamard.divisorComplementPartialProduct_def _root_.Erdos970.Complex.Hadamard.divisorPartialProduct_def _root_.Erdos970.Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI


/-!
# Convergence and holomorphy of divisor-indexed canonical products

This file proves uniform convergence on compacts, locally uniform convergence, holomorphy, and the
genus-one logarithmic-derivative identity for the divisor-indexed canonical product
`Complex.Hadamard.divisorCanonicalProduct`, under the standard summability hypothesis.

It also provides finiteness lemmas for subsets of the divisor index type cut out by a norm bound.
-/


open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

/-!
## Finiteness of “small” divisor indices
-/

/-!
## Uniform convergence on compact sets
-/

lemma norm_div_le_half_of_norm_le_of_two_mul_lt {z a : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ ≤ R) (ha : (2 * R : ℝ) < ‖a‖) :
    ‖z / a‖ ≤ (1 / 2 : ℝ) := by
  have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hR]
  have hinv : ‖a‖⁻¹ < (2 * R)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt h2R_pos ha
  have hmul_le : ‖z‖ * ‖a‖⁻¹ ≤ R * ‖a‖⁻¹ :=
    mul_le_mul_of_nonneg_right hz (inv_nonneg.2 (norm_nonneg a))
  have hmul_lt : R * ‖a‖⁻¹ < R * (2 * R)⁻¹ :=
    mul_lt_mul_of_pos_left hinv hR
  have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
    have hRne : (R : ℝ) ≠ 0 := hR.ne'
    rw [show R * (2 * R)⁻¹ = R / (2 * R) by simp [div_eq_mul_inv]]
    field_simp [hRne]
  have hnorm : ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := by
    simp [div_eq_mul_inv]
  exact le_of_lt <| by
    calc
      ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := hnorm
      _ ≤ R * ‖a‖⁻¹ := hmul_le
      _ < R * (2 * R)⁻¹ := hmul_lt
      _ = (1 / 2 : ℝ) := hRhalf

/-- The genus-one logarithmic-derivative zero terms are summable away from the zero set whenever
the genus-one divisor product is summable. -/
theorem summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) := by
  let R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hzle : ‖z‖ ≤ R := le_max_left _ _
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (2 * R) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ))
  have hu : Summable u := h_sum.mul_left (2 * R)
  refine hu.of_norm_bounded_eventually ?_
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤
          2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite
        (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  filter_upwards [h_big] with p hp
  let a : ℂ := divisorZeroIndex₀_val p
  have ha0 : a ≠ 0 := divisorZeroIndex₀_val_ne_zero p
  have hza0 : z - a ≠ 0 := sub_ne_zero.mpr (hz p)
  have hterm : 1 / (z - a) + 1 / a = z / (a * (z - a)) := by
    field_simp [ha0, hza0]
    ring
  have htri : ‖a‖ ≤ ‖z‖ + ‖z - a‖ := by
    have hraw : ‖a‖ ≤ ‖z‖ + ‖a - z‖ := by
      have h := norm_add_le z (a - z)
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    simpa [norm_sub_rev] using hraw
  have hza_lower : ‖a‖ / 2 ≤ ‖z - a‖ := by
    nlinarith [htri, hzle, hp]
  have hnorm : ‖1 / (z - a) + 1 / a‖ ≤ (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by
    rw [hterm, norm_div, norm_mul]
    have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have hza_norm_pos : 0 < ‖z - a‖ := norm_pos_iff.mpr hza0
    rw [div_eq_mul_inv]
    calc
      ‖z‖ * (‖a‖ * ‖z - a‖)⁻¹
          = ‖z‖ * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              field_simp [ha_norm_pos.ne', hza_norm_pos.ne']
      _ ≤ R * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              gcongr
      _ ≤ R * ‖a‖⁻¹ * (2 * ‖a‖⁻¹) := by
              gcongr
              have hhalf_pos : 0 < ‖a‖ / 2 := by positivity
              have hinv : ‖z - a‖⁻¹ ≤ (‖a‖ / 2)⁻¹ := by
                simpa [one_div] using one_div_le_one_div_of_le hhalf_pos hza_lower
              have hhalf_inv : (‖a‖ / 2)⁻¹ = 2 * ‖a‖⁻¹ := by field_simp [ha_norm_pos.ne']
              simpa [hhalf_inv] using hinv
      _ = (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by ring
  simpa [u, a] using hnorm

theorem hasProdUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ)) K := by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let g : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 2 * R} :
            Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    have hzle : ‖z‖ ≤ R := hnormK z hzK
    have hz_div : ‖z / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
      exact norm_div_le_half_of_norm_le_of_two_mul_lt hRpos hzle hp
    have hE :
        ‖weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1‖ ≤
          4 * ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z / divisorZeroIndex₀_val p) hz_div
    have hz_pow :
        ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
      have : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
          ‖z‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
      gcongr
    dsimp [g, u]
    nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    have hcontE : Continuous (fun z : ℂ => weierstrassFactor m z) :=
      (differentiable_weierstrassFactor m).continuous
    have hdiv : Continuous fun z : ℂ => z / divisorZeroIndex₀_val p := by
      simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
    have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
      hcontE.comp hdiv
    simpa only [g] using hcont.continuousOn.fun_sub continuous_const.continuousOn
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  simpa [g, divisorCanonicalProduct, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using! hprod

/-!
## Entire-ness (holomorphy) of the divisor-indexed canonical product
-/

theorem hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      (Set.univ : Set ℂ) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (g := divisorCanonicalProduct m f (Set.univ : Set ℂ))
      (s := (Set.univ : Set ℂ)) isOpen_univ ?_
  intro K hKU hK
  simpa using
    (hasProdUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) (K := K) hK h_sum)

theorem differentiableOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn] using
      (hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum)
  have hF :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ
          (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
          (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    have hdiff :
        Differentiable ℂ
          (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)) := by
      let F : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
        fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      have hF' : ∀ p ∈ s, Differentiable ℂ (F p) := by
        intro p hp
        have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
          have : Differentiable ℂ (fun z : ℂ => z * ((divisorZeroIndex₀_val p)⁻¹)) :=
            (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).mul_const
              ((divisorZeroIndex₀_val p)⁻¹)
          simp [div_eq_mul_inv]
        exact (differentiable_weierstrassFactor m).comp hdiv
      simpa [F] using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := F) (u := s) hF')
    simpa using hdiff.differentiableOn
  have : (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ

/-- Pointwise differentiability of the divisor-indexed canonical product under the standard
summability hypothesis. -/
theorem differentiableAt_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    DifferentiableAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
  ((differentiableOn_divisorCanonicalProduct_univ m f h_sum) z (by simp)).differentiableAt
    (by simp)

/-!
## Logarithmic derivative of the genus-one divisor product
-/

/-- The logarithmic derivative of a genus-one divisor canonical product is the expected sum of
zero terms.  The logarithmic-derivative term summability is derived from the genus-one divisor
summability and the assumption that the evaluation point is not one of the indexed zeros. -/
theorem logDeriv_divisorCanonicalProduct_one_eq_tsum
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p)
    (hprod_ne : divisorCanonicalProduct 1 f (Set.univ : Set ℂ) z ≠ 0) :
    logDeriv (divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z =
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p w => weierstrassFactor 1 (w / divisorZeroIndex₀_val p)
  have hf : ∀ p, Φ p z ≠ 0 := by
    intro p
    have hp0 : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
    refine weierstrassFactor_ne_zero_of_ne_one 1 ?_
    intro h
    exact hz p ((div_eq_one_iff_eq hp0).1 h)
  have hd : ∀ p, DifferentiableOn ℂ (Φ p) (Set.univ : Set ℂ) := by
    intro p
    have hdiv : Differentiable ℂ (fun w : ℂ => w / divisorZeroIndex₀_val p) := by
      have : Differentiable ℂ (fun w : ℂ => w * ((divisorZeroIndex₀_val p)⁻¹)) :=
        (differentiable_id : Differentiable ℂ (fun w : ℂ => w)).mul_const
          ((divisorZeroIndex₀_val p)⁻¹)
      simp [div_eq_mul_inv]
    exact ((differentiable_weierstrassFactor 1).comp hdiv).differentiableOn
  have hm' : Summable fun p => logDeriv (Φ p) z := by
    have hm :
        Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) :=
      summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq h_sum hz
    refine hm.congr ?_
    intro p
    have hp0 : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
    simpa [Φ] using
      (Complex.logDeriv_weierstrassFactor_one_div
        (a := divisorZeroIndex₀_val p) (z := z) hp0 (hz p)).symm
  have htend : MultipliableLocallyUniformlyOn Φ (Set.univ : Set ℂ) := by
    have hprod := hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
      (m := 1) (f := f) h_sum
    simpa [Φ, divisorCanonicalProduct] using hprod.multipliableLocallyUniformlyOn
  have hnez : (∏' p, Φ p z) ≠ 0 := by
    simpa [Φ, divisorCanonicalProduct] using hprod_ne
  have hlog : logDeriv (∏' p, Φ p ·) z = ∑' p, logDeriv (Φ p) z :=
    logDeriv_tprod_eq_tsum (s := (Set.univ : Set ℂ)) isOpen_univ (by simp)
      hf hd hm' htend hnez
  calc
    logDeriv (divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z
        = ∑' p, logDeriv (Φ p) z := by
          simpa [Φ, divisorCanonicalProduct] using! hlog
    _ = ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          (1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) := by
          refine tsum_congr fun p => ?_
          have hp0 : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
          simpa [Φ] using
            Complex.logDeriv_weierstrassFactor_one_div
              (a := divisorZeroIndex₀_val p) (z := z) hp0 (hz p)

end Complex.Hadamard
end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_DivisorFiber
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_one_of_mem _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem _root_.Erdos970.Complex.Hadamard.divisorComplementPartialProduct_def _root_.Erdos970.Complex.Hadamard.divisorPartialProduct_def _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI


/-!
# Fibers of the divisor index type

This file studies the fiber `{p : divisorZeroIndex₀ f univ | divisorZeroIndex₀_val p = z₀}`.
It provides a canonical `Finset` for this fiber and identifies its cardinality with the divisor
multiplicity and (for holomorphic functions) with `analyticOrderNatAt`.
-/


noncomputable section

open Set
open scoped Topology BigOperators

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

/-!
## Divisor values vs analytic order (holomorphic functions)
-/

/-!
## The multiplicity fiber is finite and has the expected cardinality
-/

theorem eventually_atTop_subset_fiberFinset
    (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s := by
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨divisorZeroIndex₀_fiberFinset (f := f) z₀, ?_⟩
  intro s hs
  exact hs

lemma not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne
    {f : ℂ → ℂ} (z₀ : ℂ) (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p ≠ z₀ := by
  simp [mem_divisorZeroIndex₀_fiberFinset]

end Complex.Hadamard
end Erdos970
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_DivisorComplement
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI


/-!
# Fiber/complement splitting for divisor-indexed partial products

This file defines finitary “partial products” of Weierstrass factors indexed by the divisor, and
develops the corresponding fiber/complement splitting. It also defines the complement canonical
product (replacing fiber factors by `1`) and proves its convergence/holomorphy properties.
-/


open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

/-!
## Complement factors

For a fixed point `z₀`, the complement factor agrees with the usual Weierstrass factor away from
the fiber over `z₀`, and is `1` on that fiber.
-/

lemma divisorComplementFactor_def
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) :
    divisorComplementFactor m f z₀ p z =
      if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
      else weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  classical
  by_cases h : divisorZeroIndex₀_val p = z₀
  · have hp : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
      simpa [mem_divisorZeroIndex₀_fiberFinset] using h
    simp [divisorComplementFactor_eq_one_of_mem, hp, h]
  · have hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
      intro hmem
      exact h ((mem_divisorZeroIndex₀_fiberFinset f z₀ p).1 hmem)
    simp [divisorComplementFactor_eq_weierstrassFactor_of_not_mem, hp, h]

/-!
## Partial products as a named function

These finite products are the approximants to the divisor-indexed canonical product.
-/

theorem differentiable_weierstrassFactor_divisorZeroIndex₀ (m : ℕ) {f : ℂ → ℂ}
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) := by
  have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
    simp [div_eq_mul_inv]
  exact (differentiable_weierstrassFactor m).comp hdiv

theorem differentiable_divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    Differentiable ℂ (divisorPartialProduct m f s) := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p)
  have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
    intro p _hp
    exact differentiable_weierstrassFactor_divisorZeroIndex₀ m p
  simpa [divisorPartialProduct, Φ] using!
    (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u := s) hΦ)

theorem analyticAt_divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    AnalyticAt ℂ (divisorPartialProduct m f s) z₀ :=
  (differentiable_divisorPartialProduct m f s).analyticAt z₀

/-!
## Splitting finite partial products into fiber vs complement

This is the finitary “fiber × complement” split.
-/

theorem differentiable_divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    Differentiable ℂ (divisorComplementPartialProduct m f z₀ s) := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => divisorComplementFactor m f z₀ p z
  have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
    intro p _hp
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · have hΦp : Φ p = fun _ => (1 : ℂ) := by
        ext z
        simp only [Φ, divisorComplementFactor_eq_one_of_mem m f z₀ p z hpF]
      rw [hΦp]
      exact differentiable_const (1 : ℂ)
    · have hΦp : Φ p = fun z => weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
        ext z
        simp only [Φ, divisorComplementFactor_eq_weierstrassFactor_of_not_mem m f z₀ p z hpF]
      rw [hΦp]
      exact differentiable_weierstrassFactor_divisorZeroIndex₀ m p
  have hEq : (fun z : ℂ => ∏ p ∈ s, Φ p z) =
      divisorComplementPartialProduct m f z₀ s := by
    ext z
    simp [Φ, divisorComplementPartialProduct]
  have : Differentiable ℂ (fun z : ℂ => ∏ p ∈ s, Φ p z) := by
    simpa using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
  simpa [hEq] using this

/-!
## Complement canonical product (fiber factors removed)

For a fixed point `z₀`, one often wants to split the infinite product into a finite “fiber part”
(`val = z₀`, accounting for the multiplicity) and an infinite “complement part” (all other indices).

The complement product is written as a total product by inserting the neutral element `1` on the
fiber indices.
-/

/-!
## Convergence/holomorphy of the complement canonical product

This is the same M-test argument as for `divisorCanonicalProduct`, but with finitely many factors
replaced by `1`. We keep the same summability hypothesis.
-/

theorem hasProdUniformlyOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        divisorComplementFactor m f z₀ p z) (divisorComplementCanonicalProduct m f z₀)
      K := by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let term : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z =>
    divisorComplementFactor m f z₀ p z
  let g : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z => term p z - 1
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 2 * R} :
          Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · have hval : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hpF
      have hu0 : 0 ≤ u p := by
        dsimp [u]
        refine mul_nonneg ?_ ?_
        · nlinarith [pow_nonneg (show 0 ≤ R from le_of_lt hRpos) (m + 1)]
        · exact pow_nonneg (inv_nonneg.2 (norm_nonneg _)) (m + 1)
      simp [g, term, divisorComplementFactor, hval, hu0, sub_eq_add_neg]
    · have hzle : ‖z‖ ≤ R := hnormK z hzK
      have hz_div : ‖z / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
        have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
        have hinv : ‖divisorZeroIndex₀_val p‖⁻¹ < (2 * R)⁻¹ := by
          simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
        have hmul_le : ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          refine mul_le_mul_of_nonneg_right hzle ?_
          exact inv_nonneg.2 (norm_nonneg _)
        have hmul_lt : R * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
          mul_lt_mul_of_pos_left hinv hRpos
        have hlt : ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
          lt_of_le_of_lt hmul_le hmul_lt
        have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
          have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
          have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
          rw [this]
          field_simp [hRne]
        have hnorm : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          simp [div_eq_mul_inv]
        have hzlt : ‖z / divisorZeroIndex₀_val p‖ < (1 / 2 : ℝ) := by
          calc
            ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := hnorm
            _ < R * (2 * R)⁻¹ := hlt
            _ = (1 / 2 : ℝ) := hRhalf
        exact le_of_lt hzlt
      have hE : ‖weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1‖ ≤
            4 * ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
        weierstrassFactor_sub_one_pow_bound (m := m) (z := z / divisorZeroIndex₀_val p) hz_div
      have hz_pow : ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
            (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        have : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          simp [div_eq_mul_inv]
        rw [this]
        have : (‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
            ‖z‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
          simp [mul_pow]
        rw [this]
        have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
        gcongr
      dsimp [g, term, u]
      simp [divisorComplementFactor, hpF] at *
      nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · have hval : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hpF
      simpa [g, term, divisorComplementFactor, hval, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) K)
    · have hvalne : divisorZeroIndex₀_val p ≠ z₀ :=
        (not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne (f := f) z₀ p).1 hpF
      have hcontE : Continuous (fun z : ℂ => weierstrassFactor m z) :=
        (differentiable_weierstrassFactor m).continuous
      have hdiv : Continuous fun z : ℂ => z / divisorZeroIndex₀_val p := by
        simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
      have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
        hcontE.comp hdiv
      have : ContinuousOn (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1) K :=
        (hcont.continuousOn.sub continuous_const.continuousOn)
      simpa [g, term, divisorComplementFactor, mem_divisorZeroIndex₀_fiberFinset, hvalne] using this
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  have hterm :
      HasProdUniformlyOn (fun p z ↦ term p z) (fun z ↦ ∏' p, term p z) K := by
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprod
  refine hterm.congr_right ?_
  intro z hz
  simp [term, divisorComplementCanonicalProduct, divisorComplementFactor]

theorem hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        divisorComplementFactor m f z₀ p z)
      (divisorComplementCanonicalProduct m f z₀)
      (Set.univ : Set ℂ) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => divisorComplementFactor m f z₀ p z)
      (g := divisorComplementCanonicalProduct m f z₀) (s := (Set.univ : Set ℂ))
      isOpen_univ ?_
  intro K hKU hK
  simpa using
    (hasProdUniformlyOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀)
      (K := K) hK h_sum)

theorem tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
        divisorComplementPartialProduct m f z₀ s)
      (divisorComplementCanonicalProduct m f z₀)
      Filter.atTop
      (Set.univ : Set ℂ) := by
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          divisorComplementFactor m f z₀ p z)
        (divisorComplementCanonicalProduct m f z₀)
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ (m := m) (f := f)
      (z₀ := z₀) h_sum
  have h :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s,
            if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
            else weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn, divisorComplementFactor, mem_divisorZeroIndex₀_fiberFinset]
      using hprod
  refine h.congr (G := fun s z => divisorComplementPartialProduct m f z₀ s z) ?_
  intro s z hz
  simp [divisorComplementPartialProduct_def]

theorem differentiableOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f)
      (z₀ := z₀) h_sum
  have hF :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ (divisorComplementPartialProduct m f z₀ s) (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    exact (differentiable_divisorComplementPartialProduct m f z₀ s).differentiableOn
  have : (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ

lemma divisorPartialProduct_eq_fiber_mul_complement_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ z : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    divisorPartialProduct m f s z =
      divisorPartialProduct m f (divisorZeroIndex₀_fiberFinset (f := f) z₀) z *
        divisorComplementPartialProduct m f z₀ s z := by
  classical -- needed
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  let P : divisorZeroIndex₀ f (Set.univ : Set ℂ) → Prop := fun p => p ∈ fiber
  let term : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => weierstrassFactor m (z / divisorZeroIndex₀_val p)
  have hfilter : s.filter P = fiber := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hs hp, hp⟩
  have hsplit :
      (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) = ∏ p ∈ s, term p := by
    simpa [term] using
      (Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := term))
  have hP : (∏ p ∈ s with P p, term p) = divisorPartialProduct m f fiber z := by
    have hg : ∀ x ∈ s \ fiber, (if x ∈ fiber then term x else (1 : ℂ)) = 1 := by
      intro x hx
      have hxnot : x ∉ fiber := (Finset.mem_sdiff.mp hx).2
      simp [hxnot]
    have hfg :
        ∀ x ∈ fiber, term x = (if x ∈ fiber then term x else (1 : ℂ)) := by
      intro x hx
      simp [hx]
    have hsub := (Finset.prod_subset_one_on_sdiff (s₁ := fiber) (s₂ := s)
        (f := term) (g := fun x => if x ∈ fiber then term x else (1 : ℂ)) hs hg hfg)
    simpa [divisorPartialProduct, term, P, fiber, Finset.prod_filter] using hsub.symm
  have hnotP : (∏ p ∈ s with ¬ P p, term p) = divisorComplementPartialProduct m f z₀ s z := by
    simp [divisorComplementPartialProduct, divisorComplementFactor, term, P, fiber,
      Finset.prod_filter, mem_divisorZeroIndex₀_fiberFinset]
  have hsplit' : ∏ p ∈ s, term p = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) :=
    hsplit.symm
  calc
    divisorPartialProduct m f s z
        = ∏ p ∈ s, term p := by simp [divisorPartialProduct, term]
    _ = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) := hsplit'
    _ = divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      simp [hP, hnotP, fiber]

end Complex.Hadamard
end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_DivisorPartialProductFactor
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI


/-!
# Local factorization of finite divisor-indexed products

This file packages the finite-order computation for partial products of Weierstrass factors indexed
by `divisorZeroIndex₀`, and deduces a local factorization at a point `z₀` once the finset contains
the full fiber over `z₀`.
-/


noncomputable section

open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

/-!
## Finite product multiplicity at a point

For a finite product of elementary factors indexed by divisor-indices, the analytic order at `z₀`
equals the number of indices whose value is exactly `z₀`.
-/

theorem analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀ = ((s.filter (fun p => divisorZeroIndex₀_val p = z₀)).card : ℕ∞) := by
  classical -- needed
  refine Finset.induction_on s ?base ?step
  · simp [analyticOrderAt_eq_zero]
  · intro p s hp hs
    by_cases hEq : divisorZeroIndex₀_val p = z₀
    · have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
      have han_fac :
          AnalyticAt ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ := by
        exact (differentiable_weierstrassFactor_divisorZeroIndex₀ m p).analyticAt z₀
      have han_rest : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m
          (z / divisorZeroIndex₀_val q)) z₀ := by
        simpa [divisorPartialProduct] using! analyticAt_divisorPartialProduct m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcard :
          (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) (insert p s)).card =
            (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) s).card + 1 := by
        simp [hEq, hp, Finset.filter_insert]
      have hfac : analyticOrderAt fac z₀ = (1 : ℕ∞) := by
        simpa [fac, hEq] using
          (analyticOrderAt_weierstrassFactor_div_self (m := m) (a := divisorZeroIndex₀_val p) hp0)
      have hrest : analyticOrderAt rest z₀ = ((s.filter
          (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
        simpa [rest] using hs
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀_val q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m
            (z / divisorZeroIndex₀_val q)) z₀ = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := hmul
        _ = (1 : ℕ∞) + ((s.filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simp [hfac, hrest]
        _ = (((insert p s).filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simp [hcard, Nat.add_comm]
    · have han_fac :
          AnalyticAt ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ := by
        exact (differentiable_weierstrassFactor_divisorZeroIndex₀ m p).analyticAt z₀
      have hfac0 : analyticOrderAt (fun z : ℂ => weierstrassFactor m
          (z / divisorZeroIndex₀_val p)) z₀ = 0 := by
        have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
        have hval : weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) ≠ 0 := by
          have : (z₀ / divisorZeroIndex₀_val p) ≠ 1 := by
            intro h1
            have : z₀ = divisorZeroIndex₀_val p := by
              have : z₀ = (z₀ / divisorZeroIndex₀_val p) * (divisorZeroIndex₀_val p) := by
                simp [div_eq_mul_inv]
              simpa [h1, div_eq_mul_inv, hp0] using this
            exact hEq (this.symm)
          exact (weierstrassFactor_ne_zero_iff m (z₀ / divisorZeroIndex₀_val p)).2 this
        simpa using (han_fac.analyticOrderAt_eq_zero).2 (by simpa using hval)
      have hcard :
          (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) (insert p s)).card =
            (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) s).card := by
        simp [hEq, Finset.filter_insert]
      have han_rest : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m
          (z / divisorZeroIndex₀_val q)) z₀ := by
        simpa [divisorPartialProduct] using! analyticAt_divisorPartialProduct m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀_val q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m
        (z / divisorZeroIndex₀_val q)) z₀
            = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt rest z₀ := by
              calc
                analyticOrderAt (fac * rest) z₀ = analyticOrderAt fac z₀ +
                    analyticOrderAt rest z₀ := hmul
                _ = analyticOrderAt rest z₀ := by
                      have hfac0' : analyticOrderAt fac z₀ = 0 := by
                        simpa [fac] using hfac0
                      simp [hfac0']
        _ = ((s.filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simpa [rest] using hs
        _ = (((insert p s).filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simpa using congrArg (fun n : ℕ => (n : ℕ∞)) hcard.symm

theorem analyticOrderAt_partialProduct_eq_fiberCard_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    analyticOrderAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀ = ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  have h :=
    analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
      (m := m) (f := f) (s := s) (z₀ := z₀)
  have hfilter :
      s.filter (fun p => divisorZeroIndex₀_val p = z₀) =
        divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    ext p
    constructor
    · intro hp'
      have hpv : divisorZeroIndex₀_val p = z₀ := (Finset.mem_filter.mp hp').2
      simpa [mem_divisorZeroIndex₀_fiberFinset] using hpv
    · intro hp_fiber
      have hpv : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hp_fiber
      have hps : p ∈ s := hs (by simpa [mem_divisorZeroIndex₀_fiberFinset] using hpv)
      exact Finset.mem_filter.2 ⟨hps, hpv⟩
  simpa [hfilter] using h

theorem exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
          =ᶠ[𝓝 z₀]
          fun z : ℂ => (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z := by
  let F : ℂ → ℂ := fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)
  have hF_ana : AnalyticAt ℂ F z₀ := by
    simpa [F, divisorPartialProduct] using! analyticAt_divisorPartialProduct m f s z₀
  have hOrder :
      analyticOrderAt F z₀ =
        ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
    simpa [F] using
      (analyticOrderAt_partialProduct_eq_fiberCard_of_subset (m := m)
      (f := f) (z₀ := z₀) (s := s) hs)
  refine (hF_ana.analyticOrderAt_eq_natCast (n := (divisorZeroIndex₀_fiberFinset
    (f := f) z₀).card)).1 ?_
  simp [hOrder]

end Complex.Hadamard
end Erdos970
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_DivisorQuotientConvergence
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI


/-!
# Quotient convergence for divisor-indexed canonical products

This file develops the convergence of quotients of finite partial products and of the
divisor-indexed canonical product by powers `(z - z₀)^k` away from `z₀`. It also proves the key
local identity on a punctured ball used later in removable-singularity arguments.
-/


open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      Filter.atTop
      (Set.univ : Set ℂ) := by
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  simpa [HasProdLocallyUniformlyOn, divisorPartialProduct] using! hprod

/-!
## Quotient convergence on compacts avoiding `z₀`

If `K` is compact and avoids `z₀`, then multiplying by `((z - z₀)^k)⁻¹` preserves uniform
convergence on `K`. -/

theorem tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) {K : Set ℂ} (hK : IsCompact K) (hKz : ∀ z ∈ K, z ≠ z₀) :
    TendstoUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      K := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_divisorPartialProduct_univ (m := m) (f := f) h_sum).mono
      (by intro z hz; simp)
  have hunif :
      TendstoUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 hloc
  let h : ℂ → ℂ := fun z => ((z - z₀) ^ k)⁻¹
  have hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C := by
    have hcont : ContinuousOn h K := by
      have hpow : ContinuousOn (fun z : ℂ => (z - z₀) ^ k) K := by
        fun_prop
      refine hpow.inv₀ ?_
      intro z hz
      have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr (hKz z hz)
      exact pow_ne_zero k hz0
    have hKimg : IsCompact (h '' K) := hK.image_of_continuousOn hcont
    rcases (isBounded_iff_forall_norm_le.1 hKimg.isBounded) with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro z hz
    exact hC (h z) ⟨z, hz, rfl⟩
  have hunif' :=
    (TendstoUniformlyOn.mul_left_bounded (p := (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f
    (Set.univ : Set ℂ)))))
        (K := K)
        (F := fun s z => divisorPartialProduct m f s z)
        (f := fun z => divisorCanonicalProduct m f (Set.univ : Set ℂ) z)
        (h := h)
        hunif hh)
  simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hunif'

/-!
## Quotient locally uniform convergence on the punctured plane `ℂ \ {z₀}`
-/

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z
      simp
    simp [hset]
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).2 ?_
  intro K hKsub hK
  have hKz : ∀ z ∈ K, z ≠ z₀ := by
    intro z hzK
    have : z ∈ (Set.univ : Set ℂ) \ {z₀} := hKsub hzK
    exact by simpa [Set.mem_sdiff, Set.mem_singleton_iff] using this.2
  exact tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m := m) (f := f) h_sum (z₀ := z₀) (k := k) (hK := hK) hKz

/-!
## Passing the fiber/complement factorization to the infinite product (punctured neighborhood)

This is the local factorization used for removability: near `z₀`, the quotient
`divisorCanonicalProduct / (z - z₀)^k` agrees (on a punctured ball) with the product of
`divisorComplementCanonicalProduct` and the analytic factor `u` coming from the fiber-only product.
-/

open _root_.Filter

theorem exists_ball_eq_divisorCanonicalProduct_div_pow_eq
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ ε > 0, ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧
      u z₀ ≠ 0 ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ →
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card =
            (divisorComplementCanonicalProduct m f z₀ z) * u z := by
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  have hfib : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z : ℂ => divisorPartialProduct m f fiber z) =ᶠ[𝓝 z₀]
            fun z : ℂ => (z - z₀) ^ fiber.card • u z := by
    simpa [fiber, divisorPartialProduct] using
      (exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, huEq⟩
  have hmem : {z : ℂ | divisorPartialProduct m f fiber z =
      (z - z₀) ^ fiber.card • u z} ∈ 𝓝 z₀ := huEq
  rcases Metric.mem_nhds_iff.1 hmem with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, u, huA, hu0, ?_⟩
  have hq :
      TendstoLocallyUniformlyOn (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
        ((Set.univ : Set ℂ) \ {z₀}) :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) (k := fiber.card)
  have hcomp :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f)
    (z₀ := z₀) h_sum
  intro z hz hzne
  have hz' : z ∈ ((Set.univ : Set ℂ) \ {z₀}) := by
    refine ⟨by simp, ?_⟩
    simpa [Set.mem_singleton_iff] using hzne
  have hF : Tendsto (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card) (Filter.atTop : Filter _)
        (𝓝 ((divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)) :=
    hq.tendsto_at hz'
  have hG0 : Tendsto  (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s z) (Filter.atTop : Filter _)
        (𝓝 (divisorComplementCanonicalProduct m f z₀ z)) :=
    hcomp.tendsto_at (by simp : z ∈ (Set.univ : Set ℂ))
  have hG : Tendsto (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorComplementPartialProduct m f z₀ s z) * u z) (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) :=
    (hG0.mul tendsto_const_nhds)
  have hsub : ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      fiber ⊆ s := eventually_atTop_subset_fiberFinset (f := f) z₀
  have heq_eventually :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
        (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card
          = (divisorComplementPartialProduct m f z₀ s z) * u z := by
    filter_upwards [hsub] with s hs
    have hsplit :
        divisorPartialProduct m f s z =
          divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      simpa [fiber] using
        (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
          (z := z) (s := s) hs)
    have hfibz :
        divisorPartialProduct m f fiber z = (z - z₀) ^ fiber.card • u z := by
      exact hball hz
    have hzpow : (z - z₀) ^ fiber.card ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hzne)
    set a : ℂ := (z - z₀) ^ fiber.card
    have ha : a ≠ 0 := by simpa [a] using hzpow
    set c : ℂ := divisorComplementPartialProduct m f z₀ s z with hc
    rw [hsplit, hfibz, smul_eq_mul]
    calc
      ((a * u z) * c) / a
          = (a * (u z * c)) / a := by simp [mul_assoc]
      _ = u z * c := by
            simpa [mul_assoc] using (mul_div_cancel_left₀ (u z * c) ha)
      _ = c * u z := by ac_rfl
      _ = (divisorComplementPartialProduct m f z₀ s z) * u z := by
            simp [c]
  have hG' :
      Tendsto
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) := by
    have heq' :
        ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
          (divisorComplementPartialProduct m f z₀ s z) * u z
            = (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card := by
      filter_upwards [heq_eventually] with s hs
      exact hs.symm
    exact (hG.congr' heq')
  exact tendsto_nhds_unique hF hG'

/-!
## Boundedness of the quotient on a punctured ball

We only need boundedness of the analytic factor `u` near `z₀`, so `ContinuousAt` at `z₀` suffices.
-/

theorem bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, BddAbove (norm ∘ (fun z : ℂ =>
      (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ''
      ((Metric.ball z₀ r) \ {z₀})) := by
  rcases exists_ball_eq_divisorCanonicalProduct_div_pow_eq (m := m) (f := f) (h_sum := h_sum)
    (z₀ := z₀) with ⟨ε, hε, u, huA, hu0, hEq⟩
  have huC : ContinuousAt u z₀ := huA.continuousAt
  have hpre : {z : ℂ | ‖u z - u z₀‖ < 1} ∈ 𝓝 z₀ := by
    have : u ⁻¹' Metric.ball (u z₀) (1 : ℝ) ∈ 𝓝 z₀ :=
      huC.preimage_mem_nhds (Metric.ball_mem_nhds (u z₀) (by norm_num))
    simpa [Metric.ball, dist_eq_norm, Set.preimage] using this
  rcases Metric.mem_nhds_iff.1 hpre with ⟨r0, hr0pos, hr0sub⟩
  set r : ℝ := min (ε / 2) r0
  have hrpos : 0 < r := lt_min (by nlinarith [hε]) hr0pos
  have hr_lt_ε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by nlinarith [hε])
  have huBound : ∀ z ∈ Metric.ball z₀ r, ‖u z‖ ≤ ‖u z₀‖ + 1 := by
    intro z hz
    have hz0 : z ∈ Metric.ball z₀ r0 := by
      have : r ≤ r0 := min_le_right _ _
      exact Metric.ball_subset_ball this hz
    have hdiff : ‖u z - u z₀‖ < 1 := hr0sub hz0
    have htri : ‖u z‖ ≤ ‖u z - u z₀‖ + ‖u z₀‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        (norm_add_le (u z - u z₀) (u z₀))
    have : ‖u z‖ ≤ 1 + ‖u z₀‖ := le_trans htri (by nlinarith [le_of_lt hdiff])
    nlinarith [this]
  have hdiffC :
      DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hcontC : ContinuousOn (divisorComplementCanonicalProduct m f z₀) (Metric.closedBall z₀ r) :=
    (hdiffC.continuousOn).mono (by intro z hz; simp)
  have hK : IsCompact (Metric.closedBall z₀ r) := isCompact_closedBall _ _
  rcases (isBounded_iff_forall_norm_le.1 (hK.image_of_continuousOn hcontC).isBounded) with ⟨C, hC⟩
  refine ⟨r, hrpos, ⟨C * (‖u z₀‖ + 1), ?_⟩⟩
  rintro _ ⟨z, hzset, rfl⟩
  rcases hzset with ⟨hzr, hzne⟩
  have hz_in_ε : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball hr_lt_ε.le hzr
  have hz_ne : z ≠ z₀ := by simpa [Set.mem_singleton_iff] using hzne
  have hq :
      (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
        = divisorComplementCanonicalProduct m f z₀ z * u z :=
    hEq z hz_in_ε hz_ne
  have hCz : ‖divisorComplementCanonicalProduct m f z₀ z‖ ≤ C := by
    have hzK : z ∈ Metric.closedBall z₀ r := Metric.mem_closedBall.2 (le_of_lt hzr)
    exact hC _ ⟨z, hzK, rfl⟩
  have huZ : ‖u z‖ ≤ ‖u z₀‖ + 1 := huBound z hzr
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) hCz
  have hmul : ‖divisorComplementCanonicalProduct m f z₀ z * u z‖ ≤ C * (‖u z₀‖ + 1) := by
    calc
      ‖divisorComplementCanonicalProduct m f z₀ z * u z‖
          = ‖divisorComplementCanonicalProduct m f z₀ z‖ * ‖u z‖ := by simp
      _ ≤ C * (‖u z₀‖ + 1) := by
            exact mul_le_mul hCz huZ (norm_nonneg _) hCnonneg
  simpa [Function.comp, hq] using hmul

/-!
## Nonvanishing of the complement canonical product near `z₀`

Pointwise, the complement canonical product is an infinite product of factors of the form `1 + aₚ`
with `∑ ‖aₚ‖` summable, hence the product is nonzero.
-/

theorem divisorComplementCanonicalProduct_ne_zero_at
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
      else weierstrassFactor m (z₀ / divisorZeroIndex₀_val p)
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ := fun p => Φ p - 1
  have hΦ_ne : ∀ p, Φ p ≠ 0 := by
    intro p
    by_cases hp : divisorZeroIndex₀_val p = z₀
    · simp [Φ, hp]
    · have hval : divisorZeroIndex₀_val p ≠ z₀ := hp
      have hz : z₀ / divisorZeroIndex₀_val p ≠ (1 : ℂ) := by
        intro h
        by_cases hp0 : divisorZeroIndex₀_val p = 0
        · have : z₀ / divisorZeroIndex₀_val p = (0 : ℂ) := by simp [hp0]
          have h01 := h
          rw [this] at h01
          exact (show False from (by simpa using (show (0 : ℂ) ≠ (1 : ℂ) from by simp) h01))
        · have : z₀ = divisorZeroIndex₀_val p := (div_eq_one_iff_eq hp0).1 h
          exact hval this.symm
      have hE : weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) ≠ 0 := by
        intro h0
        have : z₀ / divisorZeroIndex₀_val p = (1 : ℂ) :=
          (weierstrassFactor_eq_zero_iff (m := m) (z := z₀ / divisorZeroIndex₀_val p)).1 h0
        exact hz this
      simp [Φ, hp, hE]
  have hz0_le : ‖z₀‖ ≤ max ‖z₀‖ 1 := le_max_left _ _
  set R : ℝ := max ‖z₀‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin : ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤
        2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ‖a p‖ ≤ u p := by
    filter_upwards [h_big] with p hp
    have ha_pos : 0 < ‖divisorZeroIndex₀_val p‖ := lt_trans (by nlinarith [hRpos]) hp
    have hz_div : ‖z₀ / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
      have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      have hinv : ‖divisorZeroIndex₀_val p‖⁻¹ < (2 * R)⁻¹ := by
        simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
      have hmul_le : ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
        exact hz0_le
      have hmul_lt : R * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
        mul_lt_mul_of_pos_left hinv hRpos
      have hlt : ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
        lt_of_le_of_lt hmul_le hmul_lt
      have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
        have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
        have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
        rw [this]
        field_simp [hRne]
      have hnorm : ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      have hzlt : ‖z₀ / divisorZeroIndex₀_val p‖ < (1 / 2 : ℝ) := by
        calc
          ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := hnorm
          _ < R * (2 * R)⁻¹ := hlt
          _ = (1 / 2 : ℝ) := hRhalf
      exact le_of_lt hzlt
    have hE :
        ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ ≤
          4 * ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z₀ / divisorZeroIndex₀_val p) hz_div
    have hz_pow :
        ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
      have : ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
          ‖z₀‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z₀‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z₀) hz0_le (m + 1)
      gcongr
    have hp_ne : divisorZeroIndex₀_val p ≠ z₀ := by
      intro h
      have : ‖divisorZeroIndex₀_val p‖ ≤ R := by
        simp [h, R]  -- `‖z₀‖ ≤ max ‖z₀‖ 1`
      exact (not_lt_of_ge this) (lt_trans (by nlinarith [hRpos]) hp)
    have ha : ‖a p‖ = ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ := by
      simp [a, Φ, hp_ne, sub_eq_add_neg]
    calc
      ‖a p‖ = ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ := ha
      _ ≤ 4 * ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) := by
            simpa [sub_eq_add_neg, add_comm] using hE
      _ ≤ 4 * (R ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) := by
            gcongr
      _ = u p := by
            simp [u, mul_assoc, mul_comm]
  have hsum_norm : Summable (fun p => ‖a p‖) := by
    refine (Summable.of_norm_bounded_eventually (E := ℝ) (f := fun p => ‖a p‖) (g := u) hu ?_)
    filter_upwards [hBound] with p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a p))] using hp
  have htprod_ne :
      (∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (1 + a p)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (R := ℂ) (f := a) (hf := fun p => by
      simpa [a, Φ, add_sub_cancel] using hΦ_ne p) hsum_norm
  have : (∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (1 + a p)) =
      divisorComplementCanonicalProduct m f z₀ z₀ := by
    simp [a, Φ, divisorComplementCanonicalProduct, divisorComplementFactor_def]
  exact by
    intro h0
    exact htprod_ne (by simpa [this] using h0)

/-!
## Eventually: partial products factor at `z₀` with the fiber multiplicity

Along `atTop`, sufficiently large partial products contain the fiber, hence each such partial
product is locally divisible by `(z - z₀)^k`, where `k` is the fiber cardinality.
-/

/-!
## On `𝓝[≠] z₀`, large partial product quotients agree with an analytic function

This is the punctured-neighborhood version of
`eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct`,
obtained by dividing the factorization by `(z - z₀)^k` away from `z₀`.
-/

end Complex.Hadamard
end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_DivisorQuotientRemovable
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI


/-!
# Removable singularities and multiplicities for divisor-indexed canonical products

Building on quotient convergence and boundedness on punctured balls, this file proves removable
singularity results and identifies the exact zero multiplicity of `divisorCanonicalProduct`.
-/


open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

/-!
## Differentiability of the quotient on `ℂ \ {z₀}`

The quotient of the infinite product by `(z - z₀)^k` is holomorphic on the punctured plane.
-/

theorem differentiableOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (k : ℕ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    DifferentiableOn ℂ (fun z : ℂ => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hdiff_prod : DifferentiableOn ℂ (divisorPartialProduct m f s) (Set.univ : Set ℂ) := by
    exact (differentiable_divisorPartialProduct m f s).differentiableOn
  have hdiff_den : DifferentiableOn ℂ (fun z : ℂ => (z - z₀) ^ k) ((Set.univ : Set ℂ) \ {z₀}) := by
    have : Differentiable ℂ (fun z : ℂ => (z - z₀) ^ k) := by
      fun_prop
    exact this.differentiableOn
  by_cases hk : k = 0
  · subst hk
    simpa [pow_zero] using! (hdiff_prod.mono (by intro z hz; exact hz.1))
  · have hne : ∀ z ∈ ((Set.univ : Set ℂ) \ {z₀}), (fun z : ℂ => (z - z₀) ^ k) z ≠ 0 := by
      intro z hz
      have hz' : z ≠ z₀ := by
        simpa [Set.mem_sdiff, Set.mem_singleton_iff] using hz.2
      exact pow_ne_zero _ (sub_ne_zero.mpr hz')
    have hdiff_inv :
        DifferentiableOn ℂ (fun z : ℂ => ((z - z₀) ^ k)⁻¹) ((Set.univ : Set ℂ) \ {z₀}) :=
      hdiff_den.inv hne
    simpa [div_eq_mul_inv] using! (hdiff_prod.mono (by intro z hz; exact hz.1)).mul hdiff_inv

theorem differentiableOn_divisorCanonicalProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z; simp
    simp [hset]
  have hconv :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) h_sum (z₀ := z₀) (k := k)
  refine hconv.differentiableOn ?_ hopen
  refine Filter.Eventually.of_forall ?_
  intro s
  exact differentiableOn_divisorPartialProduct_div_pow_sub (m := m) (f := f) (z₀ := z₀) (k := k) s

/-!
## Removable singularity for the quotient at `z₀`

Using punctured-ball boundedness and punctured differentiability, we obtain a holomorphic extension
of the quotient at `z₀` via `Mathlib.Analysis.Complex.RemovableSingularity`.
-/

theorem differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, DifferentiableOn ℂ (Function.update
          (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
            (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) z₀
          (limUnder (𝓝[≠] z₀) (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
                (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)))
        (Metric.ball z₀ r) := by
  rcases bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall (m := m) (f := f)
      (h_sum := h_sum) (z₀ := z₀) with ⟨r, hrpos, hbdd⟩
  refine ⟨r, hrpos, ?_⟩
  have hnhds : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hdiff : DifferentiableOn ℂ (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      ((Metric.ball z₀ r) \ {z₀}) := by
    have hglob :=
      differentiableOn_divisorCanonicalProduct_div_pow_sub
        (m := m) (f := f) h_sum (z₀ := z₀)
        (k := (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
    refine hglob.mono ?_
    intro z hz
    exact ⟨by simp, hz.2⟩
  have hb : BddAbove (norm ∘ (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
      (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ''
    ((Metric.ball z₀ r) \ {z₀})) := hbdd
  simpa using
    (Complex.differentiableOn_update_limUnder_of_bddAbove (f := fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      (s := Metric.ball z₀ r) (c := z₀) hnhds hdiff hb)

theorem analyticAt_update_limUnder_divisorCanonicalProduct_div_pow
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : AnalyticAt ℂ (Function.update (fun z : ℂ =>
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) z₀
        (limUnder (𝓝[≠] z₀) (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)))
      z₀ := by
  rcases
      differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow
        (m := m) (f := f) h_sum (z₀ := z₀) with ⟨r, hrpos, hdiff⟩
  let g : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
  have hcont : ContinuousAt g z₀ :=
    (hdiff.differentiableAt (Metric.ball_mem_nhds z₀ hrpos)).continuousAt
  have hd :
      ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z := by
    have hballWithin : Metric.ball z₀ r ∈ 𝓝[≠] z₀ := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ?_
      refine ⟨Metric.ball z₀ r, Metric.ball_mem_nhds z₀ hrpos, ?_⟩
      intro z hz
      exact hz.1
    filter_upwards [hballWithin] with z hz
    exact (hdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  simpa [g] using Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont

/-- A removable analytic quotient for
`divisorCanonicalProduct m f univ z / (z - z₀)^k`, where `k` is the divisor fiber cardinality at
`z₀`. -/
theorem exists_analyticAt_divisorCanonicalProduct_quotient
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ q : ℂ → ℂ,
      AnalyticAt ℂ q z₀ ∧
        q z₀ =
          limUnder (𝓝[≠] z₀) (fun z : ℂ =>
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ∧
        ∀ z : ℂ, z ≠ z₀ →
          q z =
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
  let q : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q] using
      analyticAt_update_limUnder_divisorCanonicalProduct_div_pow
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀)
  · simp [q]
  · intro z hz
    simp [q, Function.update_of_ne hz]

/-!
## Exact multiplicity of the divisor canonical product

At each `z₀`, the zero multiplicity of `divisorCanonicalProduct` equals the fiber cardinality
`card (divisorZeroIndex₀_fiberFinset z₀)`.
-/

theorem analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
  set k : ℕ := (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  let q0 : ℂ → ℂ := fun z => F z / (z - z₀) ^ k
  rcases exists_analyticAt_divisorCanonicalProduct_quotient
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) with
    ⟨q, hqA, hq_self, hq_ne⟩
  have hdiff_univ : DifferentiableOn ℂ F (Set.univ : Set ℂ) :=
    differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have han : AnalyticAt ℂ F z₀ := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro z
    have : DifferentiableWithinAt ℂ F (Set.univ : Set ℂ) z := hdiff_univ z (by simp)
    exact this.differentiableAt (by simp)
  rcases
      exists_ball_eq_divisorCanonicalProduct_div_pow_eq (m := m) (f := f) (h_sum := h_sum)
      (z₀ := z₀)
    with ⟨ε, hε, u, huA, hu0, hEq⟩
  let g : ℂ → ℂ := fun z => (divisorComplementCanonicalProduct m f z₀ z) * u z
  have hcompDiff : DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀)
      (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hcompCont : ContinuousAt (divisorComplementCanonicalProduct m f z₀) z₀ :=
    (hcompDiff z₀ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.continuousAt
  have hgCont : ContinuousAt g z₀ := (hcompCont.mul huA.continuousAt)
  have hg0 : g z₀ ≠ 0 := by
    have hcomp0 : divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 :=
      divisorComplementCanonicalProduct_ne_zero_at (m := m) (f := f) (z₀ := z₀) h_sum
    exact mul_ne_zero hcomp0 hu0
  have hne_mem : ∀ᶠ z in 𝓝[≠] z₀, z ∈ (({z₀} : Set ℂ)ᶜ) :=
    Filter.eventually_of_mem
      (self_mem_nhdsWithin : (({z₀} : Set ℂ)ᶜ) ∈ 𝓝[≠] z₀) (fun _ hz => hz)
  have hne : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ := by
    filter_upwards [hne_mem] with z hz
    simpa [Set.mem_compl_singleton_iff] using hz
  have ht_q0 : Tendsto q0 (𝓝[≠] z₀) (𝓝 (g z₀)) := by
    have hball : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Metric.ball z₀ ε :=
      Filter.eventually_of_mem
        (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hε)) (fun _ hz => hz)
    have heq : q0 =ᶠ[𝓝[≠] z₀] g := by
      filter_upwards [hball, hne] with z hz hzne
      have hq := hEq z hz hzne
      simpa [q0, F, k, g, smul_eq_mul] using hq
    exact (hgCont.continuousWithinAt.tendsto.congr' heq.symm)
  have hlim : limUnder (𝓝[≠] z₀) q0 = g z₀ := ht_q0.limUnder_eq
  have hq0 : q z₀ ≠ 0 := by
    have hq_self' : q z₀ = limUnder (𝓝[≠] z₀) q0 := by
      simpa [q0, F, k] using hq_self
    have : q z₀ = g z₀ := hq_self'.trans hlim
    exact this.symm ▸ hg0
  have heq_punct : (fun z : ℂ => F z) =ᶠ[𝓝[≠] z₀] fun z : ℂ => (z - z₀) ^ k • q z := by
    filter_upwards [hne] with z hz
    have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
    have hq : q z = q0 z := by simpa [q0, F, k] using hq_ne z hz
    have hmul : (z - z₀) ^ k * q0 z = F z := by
      calc
        (z - z₀) ^ k * q0 z
            = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                simp [q0, div_eq_mul_inv, mul_assoc]
        _ = F z := by
              simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) hzpow)
    have : F z = (z - z₀) ^ k * q z := by
      calc
        F z = (z - z₀) ^ k * q0 z := hmul.symm
        _ = (z - z₀) ^ k * q z := by simp [hq]
    simpa [smul_eq_mul] using this
  have hcontF : ContinuousAt F z₀ :=
    (hdiff_univ z₀ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.continuousAt
  have hcontq : ContinuousAt q z₀ := hqA.continuousAt
  have h_at_z0 : F z₀ = (z₀ - z₀) ^ k • q z₀ := by
    have ht1 : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)) := hcontF.continuousWithinAt.tendsto
    have hpow :
        Tendsto (fun z : ℂ => (z - z₀) ^ k) (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k)) :=
      ((continuousAt_id.sub continuousAt_const).pow k).continuousWithinAt.tendsto
    have ht2 :
        Tendsto (fun z : ℂ => (z - z₀) ^ k • q z) (𝓝[≠] z₀)
          (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      hpow.mul (hcontq.continuousWithinAt.tendsto)
    have ht2' : Tendsto F (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      ht2.congr' heq_punct.symm
    exact tendsto_nhds_unique ht1 ht2'
  have hfac : ∀ᶠ z in 𝓝 z₀, F z = (z - z₀) ^ k • q z := by
    have hball1 : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ (by norm_num)
    have hball1' : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball z₀ 1 :=
      Filter.eventually_of_mem hball1 (fun _ hz => hz)
    filter_upwards [hball1'] with z _hz
    by_cases hz0 : z = z₀
    · subst hz0
      simpa using h_at_z0
    · have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz0)
      have hq : q z = q0 z := by simpa [q0, F, k] using hq_ne z hz0
      have hmul : (z - z₀) ^ k * q0 z = F z := by
        calc
          (z - z₀) ^ k * q0 z
              = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                  simp [q0, div_eq_mul_inv, mul_assoc]
          _ = F z := by
                simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) hzpow)
      have : F z = (z - z₀) ^ k * q z := by
        calc
          F z = (z - z₀) ^ k * q0 z := hmul.symm
          _ = (z - z₀) ^ k * q z := by simp [hq]
      simpa [smul_eq_mul] using this
  have hk' : analyticOrderAt F z₀ = k :=
    (han.analyticOrderAt_eq_natCast (n := k)).2 ⟨q, hqA, hq0, hfac⟩
  have hkNat : analyticOrderNatAt F z₀ = k := by
    simp [analyticOrderNatAt, hk']
  simpa [F, k] using hkNat

/-!
## Canonical product has the same analytic order as `f` away from the origin

Away from `0`, the analytic order of the divisor-indexed canonical product agrees with that of `f`
(for differentiable `f`), assuming the standard summability hypothesis.
-/

end Complex.Hadamard
end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_Divisor
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI


/-!
# Hadamard factorization (preliminaries)

This file develops preliminary lemmas towards Hadamard factorization for entire functions on `ℂ`.
Zeros are indexed with multiplicity using `MeromorphicOn.divisor`, then assembled into the
corresponding canonical product.

## Main definitions

- `Complex.Hadamard.divisorZeroIndex`, `Complex.Hadamard.divisorZeroIndex₀`: index types enumerating
  zeros with multiplicity.
- `Complex.Hadamard.divisorCanonicalProduct`: the canonical product indexed by `divisorZeroIndex₀`.
- `Complex.Hadamard.divisorComplementCanonicalProduct`: the canonical product with the fiber over a
  fixed point `z₀` removed.

## Main results

- The support of the divisor is discrete and countable, and meets compact sets in finitely many
  points.
- Under the standard summability hypothesis, the canonical product converges uniformly on compact
  sets, and its analytic order agrees with the expected multiplicity away from `0`.
-/


namespace Erdos970.Complex
namespace Hadamard
open _root_.Complex

/-!
## Nonvanishing helpers for Weierstrass factors
-/

open scoped Topology
open _root_.Set

/-!
## Local finiteness on compact sets

For `D : Function.locallyFinsuppWithin U ℤ`, the support is *locally finite within `U`*.
Hence any compact `K ⊆ U` meets `D.support` only finitely often.

This yields “eventually in `cofinite`” bounds for divisor-indexed products.
-/

/-!
## Entire functions are never locally zero (under a global nontriviality witness)

If `f` is differentiable on `ℂ` and not identically zero, then it is not locally zero anywhere,
hence `analyticOrderAt f z ≠ ⊤` for all `z`.
-/

lemma analyticOrderAt_ne_top_of_exists_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
  rcases hnot with ⟨z1, hz1⟩
  have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
    intro z hz
    exact (Differentiable.analyticAt (f := f) hf z)
  have hz1_not_top : analyticOrderAt f z1 ≠ ⊤ := by
    have : analyticOrderAt f z1 = 0 :=
      (hf.analyticAt z1).analyticOrderAt_eq_zero.2 hz1
    simp [this]
  intro z
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf := hf_an)
    (U := (Set.univ : Set ℂ)) (x := z1) (y := z) (by simpa using isPreconnected_univ)
    (by simp) (by simp) hz1_not_top

/-!
## Avoiding zeros on a circle

If `f` is entire and not identically zero, and if a radius `r > 0` is different from the norms of
all (nonzero) divisor-indexed zeros inside an ambient bound `B`, then `f` has no zeros on the circle
`‖z‖ = r`.
-/

/-!
## The divisor canonical product vanishes at indexed zeros

If one of the factors is `0` at `z`, then the infinite product is `0`.
-/

/-!
## The fiber finite product has the expected order at `z₀`

This packages the finite multiplicity calculation for the specific finset corresponding to the fiber
`{p | divisorZeroIndex₀_val p = z₀}`.
-/

/-!
## Exact multiplicity of the divisor canonical product

The infinite canonical product has precisely the zero multiplicities encoded by the divisor index.
The proof is supplied by the quotient/removable-singularity layer, and the
statements here record the multiplicity theorem at the level where the product is introduced.
-/

/-- The analytic order of the divisor-indexed canonical product at `z₀` is the number of
divisor indices lying over `z₀`. -/
theorem analyticOrderAt_divisorCanonicalProduct_eq_fiber_card
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  have hNat :
      analyticOrderNatAt F z₀ = (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
    simpa [F] using
      (analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀))
  have hdiffOn : DifferentiableOn ℂ F (Set.univ : Set ℂ) := by
    simpa [F] using differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have hdiff : Differentiable ℂ F := by
    intro z
    exact (hdiffOn z (by simp)).differentiableAt (by simp)
  have hnotTop : analyticOrderAt F z₀ ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hdiff)
      ⟨0, by simp [F, divisorCanonicalProduct_zero]⟩ z₀
  have hcast : (analyticOrderNatAt F z₀ : ℕ∞) = analyticOrderAt F z₀ :=
    Nat.cast_analyticOrderNatAt (f := F) (z₀ := z₀) hnotTop
  have hNatCast :
      (analyticOrderNatAt F z₀ : ℕ∞) =
        ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
    simp [hNat]
  simpa [F, hcast] using hNatCast

/-- Away from the indexed divisor, the divisor canonical product is nonzero. -/
theorem divisorCanonicalProduct_ne_zero_of_forall_ne
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    {z : ℂ} (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p) :
    divisorCanonicalProduct m f (Set.univ : Set ℂ) z ≠ 0 := by
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  have hfiber_empty : divisorZeroIndex₀_fiberFinset (f := f) z = ∅ := by
    ext p
    constructor
    · intro hp
      exact False.elim (hz p ((mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z) p).1 hp).symm)
    · intro hp
      simp at hp
  have horder :
      analyticOrderAt F z = (0 : ℕ∞) := by
    have h :=
      analyticOrderAt_divisorCanonicalProduct_eq_fiber_card
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z)
    simpa [F, hfiber_empty] using h
  have han : AnalyticAt ℂ F z := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro w
    exact (((differentiableOn_divisorCanonicalProduct_univ m f h_sum) w
      (by simp)).differentiableAt (by simp))
  exact (han.analyticOrderAt_eq_zero).1 horder

/-- The logarithmic derivative of a genus-one divisor canonical product away from its indexed
divisor, with product nonvanishing derived from the exact zero-multiplicity theorem. -/
theorem logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p) :
    logDeriv (divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z =
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) :=
  logDeriv_divisorCanonicalProduct_one_eq_tsum h_sum hz
    (divisorCanonicalProduct_ne_zero_of_forall_ne 1 f h_sum hz)

/-!
## Refining the factorization: factoring out `(z - z₀)^k` using the fiber-only product

When `s` contains the fiber finset, we can write the partial product as

`divisorPartialProduct s = (z - z₀)^k • (divisorComplementPartialProduct s * u)`

where `u` is the analytic quotient coming from the fiber-only product.
-/


end Hadamard
end Complex
end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_SpecialFunctions_Log_ExpGrowth
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Exponential bounds from logarithmic growth

Pointwise comparisons between `log (1 + ‖f x‖)`, `‖f x‖`, and `exp (C * r(x)^τ)` for
`r(x) ≥ 1`. Used in finite-order entire function theory and Hadamard factorization.

Also includes the real floor midpoint lemma used to match Weierstrass genus `⌊ρ⌋`.

## Main results

* `Real.log_norm_le_log_one_add_norm`, `Real.log_nonneg_mul_inv_norm_of_norm_le` : norm/log
  comparisons for growth bounds
* `Real.norm_le_exp_mul_rpow_of_log_growth`, `Real.log_growth_of_norm_le_exp_mul_rpow` :
  convert between log-growth and exp bounds
* `Real.sq_le_exp_const_mul_rpow` : absorb a quadratic factor into any positive exponential
  `rpow` margin
* `Real.exists_between_self_and_floor_add_one_same_floor` : genus-preserving midpoint exponent
* `Real.log_norm_le_of_log_one_add_growth_on_sphere` : sphere log-growth bound for Jensen's formula

## Tags

logarithm, exponential growth, finite order, Hadamard factorization
-/


namespace Real

variable {α E : Type*} [SeminormedAddCommGroup E]

/-- For nonzero norm, `log ‖w‖ ≤ log (1 + ‖w‖)`. -/
theorem log_norm_le_log_one_add_norm (w : E) :
    Real.log ‖w‖ ≤ Real.log (1 + ‖w‖) := by
  by_cases h0 : ‖w‖ = 0
  · simp [h0]
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm h0)
    exact Real.log_le_log hpos (by linarith [norm_nonneg w])

variable {F : Type*} [NormedAddCommGroup F]

/-- If `‖z‖ ≤ r`, then `log (r * ‖z‖⁻¹) ≥ 0`. -/
theorem log_nonneg_mul_inv_norm_of_norm_le {z : F} {r : ℝ} (hz : ‖z‖ ≤ r) :
    0 ≤ Real.log (r * ‖z‖⁻¹) := by
  by_cases hz0 : z = 0
  · simp [hz0]
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have : (1 : ℝ) ≤ r * ‖z‖⁻¹ := by
      have : (1 : ℝ) ≤ r / ‖z‖ := (one_le_div hzpos).2 hz
      simpa [div_eq_mul_inv] using this
    exact Real.log_nonneg this

/-- If `z ≠ 0` and `‖z‖ ≤ R`, then `log 2 ≤ log (2R * ‖z‖⁻¹)`. -/
theorem log_two_le_log_two_mul_mul_inv_norm_of_norm_le {z : F} {R : ℝ} (hz0 : z ≠ 0)
    (hz : ‖z‖ ≤ R) :
    Real.log 2 ≤ Real.log ((2 * R) * ‖z‖⁻¹) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hRdiv : (1 : ℝ) ≤ R / ‖z‖ := (one_le_div hzpos).2 hz
  have hle2 : (2 : ℝ) ≤ (2 * R) * ‖z‖⁻¹ := by
    have : (2 : ℝ) ≤ 2 * (R / ‖z‖) := by nlinarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  exact Real.log_le_log (by norm_num) hle2

open Metric Complex

/-- On the sphere of radius `|R|`, a log `(1 + ‖f‖)` growth bound controls `log ‖f‖`. -/
theorem log_norm_le_of_log_one_add_growth_on_sphere {f : ℂ → ℂ} {C ρ R : ℝ}
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) |R|) : log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
  have hz_norm : ‖z‖ = |R| := by
    simpa [mem_sphere, dist_zero_right] using hz
  simpa [hz_norm] using le_trans (log_norm_le_log_one_add_norm (f z)) (hC z)

end Real
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_ValueDistribution_LogCounting_Basic
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Extra logarithmic counting API

This file collects basic logarithmic-counting identities used by the Hadamard factorization API.
-/


open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

/-!
### Support of `toClosedBall`

On the closed ball of radius `|r|`, evaluation agrees with the original function; support points
lie in that ball and correspond bijectively with support points of the original function inside it.
-/

/-- A support point of `toClosedBall r D` lies in the closed ball of radius `|r|`. -/
lemma norm_le_abs_of_mem_toClosedBall_support {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : ‖z‖ ≤ |r| := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := (toClosedBall r D).supportWithinDomain hz
  simpa [mem_closedBall, dist_zero_right] using hz_ball

/-- If `‖z‖ ≤ |r|`, then `toClosedBall r D` agrees with `D` at `z`. -/
lemma toClosedBall_eval_eq_of_norm_le_abs {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : ‖z‖ ≤ |r|) : toClosedBall r D z = D z := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := by
    simpa [mem_closedBall, dist_zero_right] using hz
  simpa using toClosedBall_eval_within (f := D) hz_ball

/-- Support inside the ball is unchanged by restriction to the closed ball. -/
lemma mem_toClosedBall_support_of_mem_support_of_norm_le_abs
    {D : locallyFinsupp E ℤ} {r : ℝ} {z : E} (hzD : z ∈ D.support) (hzR : ‖z‖ ≤ |r|) :
    z ∈ (toClosedBall r D).support := by
  rw [Function.mem_support]
  rw [toClosedBall_eval_eq_of_norm_le_abs hzR]
  rwa [Function.mem_support] at hzD

/-- Support points of `toClosedBall r D` lie in the support of `D`. -/
lemma mem_support_of_mem_toClosedBall_support {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : z ∈ D.support := by
  have hnorm : ‖z‖ ≤ |r| := norm_le_abs_of_mem_toClosedBall_support hz
  rw [Function.mem_support] at hz ⊢
  rw [toClosedBall_eval_eq_of_norm_le_abs hnorm] at hz
  exact hz

end Function.locallyFinsuppWithin

namespace Function.locallyFinsuppWithin

/-- Jensen's formula for the zero-divisor of an entire function on `ℂ`. -/
theorem logCounting_divisor_eq_circleAverage_sub_const_of_differentiable
    {R : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hR : R ≠ 0) :
    logCounting (divisor f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hmero : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  simpa [top_eq_univ] using
    logCounting_divisor_eq_circleAverage_sub_const (f := f) hmero hR

end Function.locallyFinsuppWithin
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_ValueDistribution_LogCounting_Growth
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Logarithmic counting from entire-function growth

Bounds on `logCounting` of the zero divisor from a logarithmic growth hypothesis on an entire
function. Used in Hadamard divisor summability and finite-order factorization.

## Main results

* `Function.locallyFinsuppWithin.logCounting_divisor_le_of_log_growth` : log-growth of order `ρ`
  controls log-counting on disks
* `Function.locallyFinsuppWithin.massClosedBall₀`, `log_two_mul_massClosedBall₀_le_logCounting` :
  compare zero mass in a ball with log-counting at twice the radius

## Tags

logarithmic counting, Jensen's formula, finite order, Hadamard factorization
-/


open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin

/--
A logarithmic growth bound on an entire function controls its divisor log-counting on a disk.
-/
theorem logCounting_divisor_le_of_log_growth {f : ℂ → ℂ} {ρ C : ℝ} (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR0 : 0 < R) :
    logCounting (divisor f (Set.univ : Set ℂ)) R
      ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have hR : R ≠ 0 := ne_of_gt hR0
  have hEq :=
    logCounting_divisor_eq_circleAverage_sub_const_of_differentiable (f := f) hf hR
  have hf_sphere : MeromorphicOn f (sphere (0 : ℂ) |R|) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hInt : CircleIntegrable (fun z : ℂ => log ‖f z‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm hf_sphere
  have hbound_circle : ∀ z ∈ sphere (0 : ℂ) |R|,
      log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
    intro z hz
    exact log_norm_le_of_log_one_add_growth_on_sphere hC hz
  have hCircleAvg_le :
      circleAverage (fun z : ℂ => log ‖f z‖) 0 R ≤ C * (1 + |R|) ^ ρ :=
    circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R)
      (f := fun z => log ‖f z‖) hInt hbound_circle
  calc
    logCounting (divisor f (Set.univ : Set ℂ)) R
        = circleAverage (fun z : ℂ => log ‖f z‖) 0 R
            - log ‖meromorphicTrailingCoeffAt f 0‖ := by
            simpa [top_eq_univ] using hEq
    _ ≤ circleAverage (fun z : ℂ => log ‖f z‖) 0 R
          + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          have :
              -log ‖meromorphicTrailingCoeffAt f 0‖
                ≤ |log ‖meromorphicTrailingCoeffAt f 0‖| :=
            neg_le_abs (log ‖meromorphicTrailingCoeffAt f 0‖)
          linarith
    _ ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          nlinarith [hCircleAvg_le]

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/--
For non-negative locally finite support, twice the ball radius gives enough log-weight to dominate
`log 2` times the mass in the ball (excluding the origin).
-/
theorem log_two_mul_massClosedBall₀_le_logCounting {D : locallyFinsupp E ℤ} (hDnonneg : 0 ≤ D)
    {R : ℝ} (hR : 1 ≤ R) :
    (log 2) * massClosedBall₀ D R ≤ logCounting D (2 * R) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  set r : ℝ := 2 * R
  have hrpos : 0 < r := by dsimp [r] <;> nlinarith
  let Dr := toClosedBall r D
  have hDr_fin : Set.Finite Dr.support := Dr.finiteSupport (isCompact_closedBall (0 : E) |r|)
  let F : Finset E := hDr_fin.toFinset
  let SR : Finset E :=
    (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset
  let S : Finset E := SR.filter fun z => z ≠ (0 : E)
  have hS_sub : S ⊆ F := by
    intro z hzS
    have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
    have hzR : z ∈ (toClosedBall R D).support := by
      exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
        hz_mem_SR
    have hz_norm_le_R : ‖z‖ ≤ R := by
      have := norm_le_abs_of_mem_toClosedBall_support hzR
      simpa [abs_of_pos hR0] using this
    have hz_norm_le_r : ‖z‖ ≤ |r| := by
      have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r] <;> nlinarith)
      simpa [abs_of_pos hrpos] using this
    have hzD : z ∈ D.support := mem_support_of_mem_toClosedBall_support hzR
    have : z ∈ Dr.support := by
      simpa [Dr] using
        mem_toClosedBall_support_of_mem_support_of_norm_le_abs (D := D) (r := r) hzD hz_norm_le_r
    exact hDr_fin.mem_toFinset.2 this
  have hlogCounting :
      logCounting D r
        = (F.sum fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * log r := by
    have hsupp : Function.support (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) ⊆ F := by
      intro z hz
      have : Dr z ≠ 0 := by
        by_contra h0
        simp [Function.mem_support, h0] at hz
      have : z ∈ Dr.support := by simpa [Function.mem_support] using this
      exact hDr_fin.mem_toFinset.2 this
    simp [logCounting, Dr, r,
      finsum_eq_sum_of_support_subset (f := fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) (s := F) hsupp]
  have hsum_le :
      (log 2) * (S.sum fun z => (D z : ℝ))
        ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := by
    have hterm_nonneg : ∀ z ∈ F, 0 ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzF
      have hz_sup : z ∈ Dr.support := hDr_fin.mem_toFinset.1 hzF
      have hDz : 0 ≤ Dr z := by
        have hDz' : 0 ≤ D z := hDnonneg z
        have hDrz : Dr z = D z :=
          toClosedBall_eval_eq_of_norm_le_abs (norm_le_abs_of_mem_toClosedBall_support hz_sup)
        simpa [hDrz] using hDz'
      have hlog : 0 ≤ log (r * ‖z‖⁻¹) := by
        have hzle : ‖z‖ ≤ r := by
          have hnorm := norm_le_abs_of_mem_toClosedBall_support hz_sup
          simpa [abs_of_pos hrpos] using hnorm
        exact log_nonneg_mul_inv_norm_of_norm_le hzle
      exact mul_nonneg (by exact_mod_cast hDz) hlog
    have hsumSF :
        S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹))
          ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub (by
        intro z hzF _; exact hterm_nonneg z hzF)
    have hterm_ge : ∀ z ∈ S, (log 2) * (D z : ℝ) ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzS
      have hz0 : z ≠ (0 : E) := (Finset.mem_filter.1 hzS).2
      have hz_norm_le_R : ‖z‖ ≤ R := by
        have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
        have hzRsup : z ∈ (toClosedBall R D).support := by
          exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
            hz_mem_SR
        have hnorm := norm_le_abs_of_mem_toClosedBall_support hzRsup
        simpa [abs_of_pos hR0] using hnorm
      have hlog_le : log 2 ≤ log (r * ‖z‖⁻¹) := by
        simpa [r] using log_two_le_log_two_mul_mul_inv_norm_of_norm_le hz0 hz_norm_le_R
      have hDz_nonneg : 0 ≤ D z := hDnonneg z
      have hz_in_ballr : z ∈ closedBall (0 : E) |r| := by
        have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r] <;> nlinarith)
        simpa [mem_closedBall, dist_zero_right, abs_of_pos hrpos] using this
      have hDrz : Dr z = D z := by
        have hz_norm_le : ‖z‖ ≤ |r| := by
          simpa [mem_closedBall, dist_zero_right] using hz_in_ballr
        simpa [Dr] using toClosedBall_eval_eq_of_norm_le_abs (D := D) (r := r) (z := z) hz_norm_le
      have : (log 2) * (D z : ℝ) ≤ (log (r * ‖z‖⁻¹)) * (D z : ℝ) :=
        mul_le_mul_of_nonneg_right hlog_le (by exact_mod_cast hDz_nonneg)
      simpa [hDrz, mul_assoc, mul_left_comm, mul_comm] using this
    calc
      (log 2) * (S.sum fun z => (D z : ℝ))
          = S.sum (fun z => (log 2) * (D z : ℝ)) := by simp [Finset.mul_sum]
      _ ≤ S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
        Finset.sum_le_sum fun z hz => hterm_ge z hz
      _ ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := hsumSF
  have hcenter_nonneg : 0 ≤ (D 0 : ℝ) * log r := by
    have hD0 : 0 ≤ D 0 := hDnonneg 0
    have hlogr : 0 ≤ log r := log_nonneg (by nlinarith [hR])
    exact mul_nonneg (by exact_mod_cast hD0) hlogr
  have : (log 2) * (S.sum fun z => (D z : ℝ)) ≤ logCounting D r := by
    rw [hlogCounting]
    nlinarith [hsum_le, hcenter_nonneg]
  simpa [massClosedBall₀, r, S, SR] using this

theorem massClosedBall₀_divisor_le_of_log_growth {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR : 1 ≤ R) :
    massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
      ≤ (C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖|) / log 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hlog2pos : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  have hlow :
      (log 2) * massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
        ≤ logCounting (divisor f (Set.univ : Set ℂ)) (2 * R) :=
    log_two_mul_massClosedBall₀_le_logCounting
      (D := divisor f (Set.univ : Set ℂ))
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (hf.differentiableOn.analyticOnNhd isOpen_univ)) hR
  have hupp :
      logCounting (divisor f (Set.univ : Set ℂ)) (2 * R)
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    have h2R0 : 0 < 2 * R := by nlinarith [hR0]
    simpa using logCounting_divisor_le_of_log_growth (f := f) (ρ := ρ) (C := C) hf hC
      (R := 2 * R) h2R0
  have hmul :
      (log 2) * massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| :=
    hlow.trans hupp
  have hmul' :
      massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R * log 2
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  exact (le_div_iff₀ hlog2pos).2 hmul'

end Function.locallyFinsuppWithin
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Meromorphic_DivisorHolomorphic
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Divisors of holomorphic functions

Holomorphic functions on `ℂ` have non-negative divisors, since zeros contribute non-negative
multiplicity and poles cannot occur.

## Main results

* `Differentiable.divisor_nonneg` : the divisor of an entire function is non-negative
-/


open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The divisor of an entire function is non-negative. -/
theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_SpecialFunctions_Log_Dyadic
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Dyadic estimates from logarithms

This file records elementary estimates for dyadic radii selected by `⌊logb 2 x⌋₊`.
The estimates are used to decompose growth bounds into summable geometric shells.
-/


noncomputable section

open scoped BigOperators
open Filter

namespace Real

/-- The dyadic lower endpoint associated to `⌊log₂ x⌋` is at most `x`, for `1 ≤ x`. -/
lemma two_pow_floor_logb_le {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlog_nonneg : 0 ≤ Real.logb 2 x :=
    Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
  have hfloor_le : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
    simpa using (Nat.floor_le hlog_nonneg)
  exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ))
    (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
    (by norm_num : (1 : ℝ) < 2) hx0).1 hfloor_le

/-- `x` lies below the next dyadic endpoint after `⌊log₂ x⌋`, for `1 ≤ x`. -/
lemma lt_two_pow_floor_logb_add_one {x : ℝ} (hx : 1 ≤ x) :
    x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
    simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
  exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
    (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1)
    (by norm_num : (1 : ℝ) < 2) hx0).1 hlt

/-- If `k = ⌊log₂ (x / r₀)⌋`, then `r₀ * 2^k` is a lower dyadic bound for `x`. -/
lemma dyadicShell_lower_bound {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ x := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hle : (2 : ℝ) ^ (k : ℝ) ≤ x / r0 := by
    have := Real.two_pow_floor_logb_le (x := x / r0) hx1
    simpa [hk] using this
  have := mul_le_mul_of_nonneg_left hle hr0.le
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  simpa [mul_assoc, hxEq] using this

/-- If `k = ⌊log₂ (x / r₀)⌋`, then `x` is bounded by the next dyadic endpoint. -/
lemma dyadicShell_upper_bound {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    x ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hlt : x / r0 < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    have := Real.lt_two_pow_floor_logb_add_one (x := x / r0) hx1
    simpa [hk] using this
  have := mul_lt_mul_of_pos_left hlt hr0
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  exact le_of_lt (by simpa [mul_assoc, hxEq] using this)

/-- Some dyadic scale is beyond any prescribed real bound. -/
lemma exists_nat_le_two_pow (A : ℝ) :
    ∃ k0 : ℕ, ∀ n ≥ k0, A ≤ (2 : ℝ) ^ n := by
  have htend : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
  exact eventually_atTop.1 ((tendsto_atTop.1 htend) A)

/-- Once the dyadic scale is past `r₀⁻¹`, the upper endpoint `r₀ 2^(k+1)` is at least `1`. -/
lemma one_le_dyadicRadius_succ_of_inv_le_two_pow
    {r0 : ℝ} {k0 kk : ℕ} (hr0 : 0 < r0)
    (hk0 : ∀ n ≥ k0, (1 / r0 : ℝ) ≤ (2 : ℝ) ^ n) (hkk : k0 ≤ kk + 1) :
    (1 : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hpow_nat : (1 / r0 : ℝ) ≤ (2 : ℝ) ^ (kk + 1) := hk0 (kk + 1) hkk
  have hpow_rpow : (1 / r0 : ℝ) ≤ (2 : ℝ) ^ ((kk : ℝ) + 1) := by
    have hcast : (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ (kk + 1) := by
      calc
        (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ ((kk + 1 : ℕ) : ℝ) := by
          simp [Nat.cast_add, Nat.cast_one]
        _ = (2 : ℝ) ^ (kk + 1) := by
          simpa using (Real.rpow_natCast (2 : ℝ) (kk + 1))
    simpa [hcast] using hpow_nat
  have : (r0 * (1 / r0) : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hpow_rpow hr0.le
  simpa [one_div, hr0ne, mul_assoc] using this

/-- A dyadic radius `r₀ 2^(k+1)` gives polynomial growth bounded by a geometric term. -/
lemma one_add_abs_two_mul_dyadicRadius_rpow_le {r0 ρ : ℝ} (k : ℕ)
    (hr0 : 0 < r0) (hρ : 0 ≤ ρ) :
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
      ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have hRk' : |2 * Rk| = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
    have hnonneg : 0 ≤ (2 : ℝ) * Rk := by
      have : 0 ≤ Rk := by
        dsimp [Rk]
        exact mul_nonneg hr0.le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      nlinarith
    have hmul : (2 : ℝ) * Rk = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
      dsimp [Rk]
      calc
        (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))
            = (2 * r0) * (2 : ℝ) ^ ((k : ℝ) + 1) := by ring
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ)) := by
              simp [Real.rpow_add, mul_assoc]
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * 2) := by simp [Real.rpow_one]
        _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by ring
    calc
      |2 * Rk| = 2 * Rk := abs_of_nonneg hnonneg
      _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := hmul
  have hbase :
      (1 + |2 * Rk|) ≤ (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) := by
        simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
      simpa [Real.rpow_natCast] using this
    have habs :
        1 + |2 * Rk| ≤ (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      rw [hRk']
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
        (add_le_add_right h1 ((4 * r0) * (2 : ℝ) ^ (k : ℝ)))
    have hfac :
        (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ)
          = (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      ring
    exact habs.trans (le_of_eq hfac)
  have hRnonneg : 0 ≤ (1 + |2 * Rk|) := by linarith [abs_nonneg (2 * Rk)]
  have :
      (1 + |2 * Rk|) ^ ρ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ :=
    Real.rpow_le_rpow hRnonneg hbase hρ
  have hsplit :
      ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ
        = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := by
    have h1 : 0 ≤ (1 + 4 * r0) := by nlinarith [hr0.le]
    have h2 : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    simpa using (Real.mul_rpow h1 h2 (z := ρ))
  have hpow : ((2 : ℝ) ^ (k : ℝ)) ^ ρ = ((2 : ℝ) ^ ρ) ^ k := by
    have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
    calc
      ((2 : ℝ) ^ (k : ℝ)) ^ ρ = (2 : ℝ) ^ ((k : ℝ) * ρ) := by
        simp [Real.rpow_mul]
      _ = ((2 : ℝ) ^ ρ) ^ (k : ℝ) := by
        simpa [mul_comm] using
          (Real.rpow_mul (x := (2 : ℝ)) (y := ρ) (z := (k : ℝ)) h2nonneg)
      _ = ((2 : ℝ) ^ ρ) ^ k := by
        simp [Real.rpow_natCast]
  calc
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
        = (1 + |2 * Rk|) ^ ρ := by rfl
    _ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ := this
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := hsplit
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
      simpa [mul_assoc] using congrArg (fun t => (1 + 4 * r0) ^ ρ * t) hpow

/-- A finite shell whose radii are bounded below contributes at most
`card * lower_radius⁻¹ ^ τ` to the inverse-power sum. -/
lemma tsum_inv_rpow_le_card_mul_of_lower_bound {α : Type*} [Fintype α] {a : α → ℝ}
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_lower : ∀ x, R ≤ a x) :
    (∑' x : α, (a x)⁻¹ ^ τ) ≤ (Fintype.card α : ℝ) * (R⁻¹ ^ τ) := by
  have hsum_le :
      (∑ x : α, (a x)⁻¹ ^ τ) ≤ ∑ _x : α, R⁻¹ ^ τ := by
    refine Finset.sum_le_sum ?_
    intro x _hx
    have hinv : (a x)⁻¹ ≤ R⁻¹ := by
      simpa using (inv_anti₀ hR (ha_lower x))
    exact Real.rpow_le_rpow (inv_nonneg.2 (ha_nonneg x)) hinv hτ.le
  simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum_le

/-- Inverse powers of dyadic radii split into the initial radius and a geometric factor. -/
lemma inv_dyadicRadius_rpow_eq (r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
      (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
  have h2k_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  calc
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0 * (2 : ℝ) ^ (k : ℝ)) ^ (-τ) := by
      simpa using (Real.rpow_neg_eq_inv_rpow (r0 * (2 : ℝ) ^ (k : ℝ)) τ).symm
    _ = r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
      simpa using (Real.mul_rpow hr0 h2k_nonneg (z := -τ))
    _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
      have hr0' : r0 ^ (-τ) = (r0⁻¹ : ℝ) ^ τ := by
        simp [Real.rpow_neg_eq_inv_rpow]
      have h2' : ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = ((2 : ℝ) ^ (-τ)) ^ k := by
        have h2nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
        calc
          ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = (2 : ℝ) ^ ((k : ℝ) * (-τ)) := by
            exact (Real.rpow_mul (x := (2 : ℝ)) (y := (k : ℝ)) (z := -τ)
              h2nonneg).symm
          _ = (2 : ℝ) ^ ((-τ) * (k : ℝ)) := by ring_nf
          _ = ((2 : ℝ) ^ (-τ)) ^ (k : ℝ) := by
            exact Real.rpow_mul (x := (2 : ℝ)) (y := -τ) (z := (k : ℝ)) h2nonneg
          _ = ((2 : ℝ) ^ (-τ)) ^ k := by
            simp [Real.rpow_natCast]
      calc
        r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ))
            = (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
              rw [hr0']
        _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
              rw [h2']

lemma two_rpow_sub_eq_mul_neg (ρ τ : ℝ) :
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  calc
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ (ρ + (-τ)) := by ring_nf
    _ = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
      simp [Real.rpow_add h2pos]

lemma two_rpow_sub_pow_eq_mul_pow (ρ τ : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ (ρ - τ)) ^ k =
      ((2 : ℝ) ^ ρ) ^ k * (((2 : ℝ) ^ (-τ)) ^ k) := by
  simp [two_rpow_sub_eq_mul_neg, mul_pow]

lemma dyadic_growth_inv_term_eq (C L M r0 ρ τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
        ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
      = (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k := by
  have hrk_inv :
      (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (-τ)) ^ k) :=
    inv_dyadicRadius_rpow_eq r0 τ k hr0
  rw [hrk_inv, two_rpow_sub_pow_eq_mul_pow]
  ac_rfl

lemma dyadic_trailing_inv_term_le (C L r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (C / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
      ≤ (((C / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
  rw [inv_dyadicRadius_rpow_eq r0 τ k hr0]
  have hcoeff : C / L ≤ C / L + 1 := by linarith
  have hr0Inv_nonneg : 0 ≤ (r0⁻¹ : ℝ) ^ τ :=
    Real.rpow_nonneg (inv_nonneg.2 hr0) _
  have hmul :
      (C / L) * ((r0⁻¹ : ℝ) ^ τ)
        ≤ ((C / L) + 1) * ((r0⁻¹ : ℝ) ^ τ) :=
    mul_le_mul_of_nonneg_right hcoeff hr0Inv_nonneg
  have hqpow_nonneg : 0 ≤ ((2 : ℝ) ^ (-τ)) ^ k :=
    pow_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)) _
  have := mul_le_mul_of_nonneg_right hmul hqpow_nonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

lemma dyadic_growth_mass_mul_inv_le_geometric {C L M X T Ctrail r0 ρ τ : ℝ} {k : ℕ}
    (hL : 0 < L) (hC : 0 ≤ C) (hr0 : 0 ≤ r0)
    (hX : X ≤ M * ((2 : ℝ) ^ ρ) ^ k)
    (hT : T ≤ ((C * X + Ctrail) / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :
    T ≤ (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k
        + (((Ctrail / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
  have hmul : C * X ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) :=
    mul_le_mul_of_nonneg_left hX hC
  have hnum : C * X + Ctrail ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail :=
    add_le_add hmul le_rfl
  have hdiv :
      (C * X + Ctrail) / L ≤ (C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L :=
    div_le_div_of_nonneg_right hnum hL.le
  have h2k_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (k : ℝ))
  have hrk_nonneg : 0 ≤ r0 * (2 : ℝ) ^ (k : ℝ) :=
    mul_nonneg hr0 h2k_nonneg
  have hfactor_nonneg : 0 ≤ ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ) :=
    Real.rpow_nonneg (inv_nonneg.2 hrk_nonneg) τ
  have hmul' :=
    mul_le_mul_of_nonneg_right hdiv hfactor_nonneg
  have hdecomp :
      ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L) *
          ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
        =
        ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
            ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
          + ((Ctrail / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) := by
    let Y : ℝ := (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ
    have :
        ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L) * Y
          = ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) * Y
            + ((Ctrail / L) * Y) := by
      ring
    simpa [Y]
  have hpre :
      T ≤ ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
            ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
          + ((Ctrail / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :=
    hT.trans (hmul'.trans_eq hdecomp)
  have hA := le_of_eq (dyadic_growth_inv_term_eq C L M r0 ρ τ k hr0)
  have hB := dyadic_trailing_inv_term_le Ctrail L r0 τ k hr0
  exact hpre.trans (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using add_le_add hA hB)

lemma two_geometric_shift_add (A B q qσ : ℝ) (k k0 : ℕ) :
    A * q ^ (k + k0) + B * qσ ^ (k + k0)
      = (A * q ^ k0) * q ^ k + (B * qσ ^ k0) * qσ ^ k := by
  rw [pow_add, pow_add]
  ac_rfl

end Real
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_HadamardFactorization_Summability
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Divisor summability from logarithmic growth

Dyadic shell summability for the zero divisor of an entire function with a logarithmic growth
bound. This is the zero-counting input for Tao's finite-order Hadamard theorem, not the
factorization conclusion itself.  It is step 1 of the intrinsic Hadamard pipeline
(`divisorCanonicalProduct`, `hadamard_factorization_of_growth`, `hadamard_factorization_of_order`).

## Main results

* `divisorMassClosedBall₀_le_of_growth` : zero mass in a ball is `O((1 + R)^ρ)` under
  log-growth of order `ρ`
* `summable_norm_inv_pow_divisorZeroIndex₀_of_growth` : growth implies convergence of the
  canonical product
* `jensen_formula_logCounting_eq_circleAverage_sub_log_trailingCoeff` : Hadamard alias for Jensen's
  formula (see also
  `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const_of_differentiable`)

Jensen's formula and log-counting growth bounds live in
`Analysis.Complex.ValueDistribution.LogCounting`.

Tao Notes 1 enters here through Theorem 2 (Jensen's formula), Proposition 8 (zero counting from
growth), and the convergence input corresponding to Exercise 19 for the genus `⌊ρ⌋` canonical
product.

## References

* [tao246bComplexAnalysis], Theorem 2 and Proposition 8 (disk formulation; compare
  `divisorMassClosedBall₀` and `logCounting`)
* [MR886677], §1 for disk automorphisms and disk canonical factors used in the counting background
* [boas1954] and [levin1980] for the Jensen/counting estimates feeding the classical Hadamard
  product theorem
-/


noncomputable section

open Filter Topology Set Complex
open scoped BigOperators Topology

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

/-!
### Lindelöf summability

A bound on `log (1 + ‖f z‖)` controls `logCounting` of the divisor and yields summability of
`‖a‖⁻¹^(m+1)` for the divisor-indexed canonical product.
-/

open scoped _root_.Real

lemma divisorMassClosedBall₀_le_of_growth {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    {R : ℝ} (hR : 1 ≤ R) :
    divisorMassClosedBall₀ f R
      ≤ (C * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) /
          Real.log 2 := by
  simpa [divisorMassClosedBall₀] using
    (Function.locallyFinsuppWithin.massClosedBall₀_divisor_le_of_log_growth
      (f := f) (ρ := ρ) (C := C) hf hC hR)

lemma exists_r0_le_norm_divisorZeroIndex₀_val {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∃ r0 : ℝ, 0 < r0 ∧
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖ := by
  classical
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  have hzero : ∀ p : divisorZeroIndex₀ f U, f (divisorZeroIndex₀_val p) = 0 := by
    intro p
    set z : ℂ := divisorZeroIndex₀_val p
    have hneTop : meromorphicOrderAt f z ≠ ⊤ := by
      have hzAnal : AnalyticAt ℂ f z := hf.analyticAt z
      have hzA : analyticOrderAt f z ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := z)
      intro htop
      have hm : meromorphicOrderAt f z = (analyticOrderAt f z).map (↑) :=
        hzAnal.meromorphicOrderAt_eq (𝕜 := ℂ)
      cases h : analyticOrderAt f z with
      | top =>
          exact hzA (by simp [h])
      | coe n =>
          have : (analyticOrderAt f z).map (↑) ≠ (⊤ : WithTop ℤ) := by
            simp [h]
          exact this (by simpa [hm] using htop)
    have hmon : MeromorphicOn f U := by
      intro w hw; exact (hf.analyticAt w).meromorphicAt
    have hdiv : MeromorphicOn.divisor f U z = (meromorphicOrderAt f z).untop₀ := by
      simpa [U] using (MeromorphicOn.divisor_apply (f := f) (U := U) (z := z) hmon (by aesop))
    have hDz : MeromorphicOn.divisor f U z ≠ 0 := by
      have hzsup : z ∈ (MeromorphicOn.divisor f U).support := by
        simp [z]
      simpa [Function.mem_support] using hzsup
    have hposZ : (0 : ℤ) < (meromorphicOrderAt f z).untop₀ := by
      have hge0 : 0 ≤ (meromorphicOrderAt f z).untop₀ := by
        have : 0 ≤ MeromorphicOn.divisor f U z := by
          simpa [D, U, z] using hDnonneg z
        simpa [hdiv] using this
      have hne0 : (meromorphicOrderAt f z).untop₀ ≠ 0 := by
        simpa [hdiv] using hDz
      exact lt_of_le_of_ne hge0 (by simpa [eq_comm] using hne0)
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f z := by
      have : (0 : WithTop ℤ) < ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) :=
        WithTop.coe_lt_coe.2 hposZ
      simpa [WithTop.coe_untop₀_of_ne_top hneTop] using this
    have htend0 : Tendsto f (𝓝[≠] z) (𝓝 (0 : ℂ)) :=
      tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := z) hpos
    have hcontz : ContinuousAt f z := (hf z).continuousAt
    have htendz : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (hcontz.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z))
    exact tendsto_nhds_unique htendz htend0
  by_cases h0 : f 0 = 0
  · have hD0 : D 0 ≠ 0 := by
      have hmero0 : MeromorphicAt f (0 : ℂ) := (hf.analyticAt 0).meromorphicAt
      have hneTop0 : meromorphicOrderAt f (0 : ℂ) ≠ ⊤ := by
        have hA0 : analyticOrderAt f (0 : ℂ) ≠ ⊤ :=
          analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := 0)
        intro htop
        have hm : meromorphicOrderAt f (0 : ℂ) = (analyticOrderAt f (0 : ℂ)).map (↑) :=
          (hf.analyticAt 0).meromorphicOrderAt_eq (𝕜 := ℂ)
        cases h : analyticOrderAt f (0 : ℂ) with
        | top => exact absurd h hA0
        | coe n =>
            have : (analyticOrderAt f (0 : ℂ)).map (↑) ≠ (⊤ : WithTop ℤ) := by
              simp [h]
            exact this (by simpa [hm] using htop)
      have htend0 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
        have : Tendsto f (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by simpa [h0] using hcont0.tendsto
        exact this.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
      have hpos0 : (0 : WithTop ℤ) < meromorphicOrderAt f (0 : ℂ) :=
        (tendsto_zero_iff_meromorphicOrderAt_pos hmero0).1 htend0
      have hpos0' : (0 : ℤ) < (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have : (0 : WithTop ℤ) < ((meromorphicOrderAt f (0 : ℂ)).untop₀ : WithTop ℤ) := by
          simpa [WithTop.coe_untop₀_of_ne_top hneTop0] using hpos0
        simpa using (WithTop.coe_lt_coe.1 this)
      have hdiv0 : D 0 = (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have hmon : MeromorphicOn f U := by
          intro w hw; exact (hf.analyticAt w).meromorphicAt
        simpa [D, U] using
          (MeromorphicOn.divisor_apply (f := f) (U := U) (z := (0 : ℂ))
            hmon (by aesop))
      exact by
        have : (meromorphicOrderAt f (0 : ℂ)).untop₀ ≠ 0 := ne_of_gt hpos0'
        simpa [hdiv0] using this
    have hmem0 : (0 : ℂ) ∈ D.support := by
      simp [Function.mem_support, hD0]
    have hdisc : IsDiscrete D.support := by
      simpa [D] using (D.discreteSupport)
    rcases Metric.exists_ball_inter_eq_singleton_of_mem_discrete hdisc hmem0 with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have hp : divisorZeroIndex₀_val p ∈ D.support := by
      simp [D, divisorZeroIndex₀_val_mem_divisor_support (f := f) (U := U) p]
    have hnotBall : divisorZeroIndex₀_val p ∉ Metric.ball (0 : ℂ) r0 := by
      intro hball
      have : divisorZeroIndex₀_val p ∈ Metric.ball (0 : ℂ) r0 ∩ D.support := ⟨hball, hp⟩
      have : divisorZeroIndex₀_val p ∈ ({(0 : ℂ)} : Set ℂ) := by simp [hr0] at this
      have : divisorZeroIndex₀_val p = 0 := by simp [Set.mem_singleton_iff] at this
      exact (divisorZeroIndex₀_val_ne_zero p) this
    have : r0 ≤ ‖divisorZeroIndex₀_val p‖ := by
      have : ¬ ‖divisorZeroIndex₀_val p‖ < r0 := by
        intro hlt
        exact hnotBall (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
      exact le_of_not_gt this
    exact this
  · have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hcont0.eventually_ne h0
    rcases Metric.mem_nhds_iff.1 hne with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have : ¬ ‖divisorZeroIndex₀_val p‖ < r0 := by
      intro hlt
      have hzball : divisorZeroIndex₀_val p ∈ Metric.ball (0 : ℂ) r0 := by
        simpa [Metric.mem_ball, dist_zero_right] using hlt
      have : f (divisorZeroIndex₀_val p) ≠ 0 := hr0 hzball
      exact this (hzero p)
    exact le_of_not_gt this

/-!
### Dyadic-shell summability for divisor-indexed zeros
-/

open scoped BigOperators

/-- The number of divisor indices in a closed ball is bounded by the divisor mass there. -/
lemma card_ball_le_divisorMassClosedBall₀
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ} (hR : 0 < R) :
    (Nat.card {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ)
      ≤ divisorMassClosedBall₀ f R := by
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have :
      Fintype {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} := by
    have : Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} := by
      have : Metric.closedBall (0 : ℂ) R ⊆ U := by simp [U]
      simpa using (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) (B := R) this)
    exact Fintype.ofFinite _
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  let T : Type :=
    Σ z : S, Fin (Int.toNat (D z.1))
  let φ :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} → T := fun p =>
    let z0 : ℂ := divisorZeroIndex₀_val p.1
    have hz0_memSR : z0 ∈ SR := by
      have hz0_norm : ‖z0‖ ≤ |R| := by
        have : ‖z0‖ ≤ R := p.2
        simpa [abs_of_pos hR] using this
      have hz0_support : z0 ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
        have hz0_suppD : z0 ∈ D.support := by
          simp [z0, D]
        exact Function.locallyFinsuppWithin.mem_toClosedBall_support_of_mem_support_of_norm_le_abs
          hz0_suppD hz0_norm
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport
          (Function.locallyFinsuppWithin.toClosedBall R D)
            (isCompact_closedBall (0 : ℂ) |R|))).2 hz0_support
    have hz0_ne0 : z0 ≠ 0 := divisorZeroIndex₀_val_ne_zero p.1
    have hz0_memS : z0 ∈ S := Finset.mem_filter.2 ⟨hz0_memSR, hz0_ne0⟩
    ⟨⟨z0, hz0_memS⟩, by
        simpa [z0, divisorZeroIndex₀_val, D] using p.1.1.2⟩
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    have hσ := (Sigma.mk.inj_iff).1 hpq
    have hzS : (φ p).1 = (φ q).1 := hσ.1
    have hz : divisorZeroIndex₀_val p.1 = divisorZeroIndex₀_val q.1 := by
      simpa [φ] using congrArg Subtype.val hzS
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext
    · exact hz
    · simpa [φ] using hσ.2
  have hcard_le :
      Fintype.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} ≤ Fintype.card T :=
    Fintype.card_le_of_injective φ hφ_inj
  have hT_card :
      (Fintype.card T : ℝ) =
        (S.sum fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
    have hNat :
        Fintype.card T = ∑ z : S, Int.toNat (D z.1) := by
      have h1 :
          Fintype.card T = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1))) := by
        change Fintype.card (Sigma (fun z : S => Fin (Int.toNat (D z.1))))
            = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1)))
        exact (Fintype.card_sigma (ι := S) (α := fun z : S => Fin (Int.toNat (D z.1))))
      simpa using h1
    have hR :
        (Fintype.card T : ℝ) = ∑ z : S, (Int.toNat (D z.1) : ℝ) := by
      exact_mod_cast hNat
    have hR' :
        (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := by
      simpa [Finset.univ_eq_attach] using hR
    calc
      (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := hR'
      _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
            simpa using (Finset.sum_attach (s := S) (f := fun z : ℂ => (Int.toNat (D z) : ℝ)))
  have htoNat_le : ∀ z ∈ S, (Int.toNat (D z) : ℝ) ≤ (D z : ℝ) := by
    intro z hz
    have hDz_nonneg : 0 ≤ D z := by simpa [D] using hDnonneg z
    have hEqZ : ((Int.toNat (D z) : ℕ) : ℤ) = D z := by
      simpa using (Int.toNat_of_nonneg hDz_nonneg)
    have hEqR : (Int.toNat (D z) : ℝ) = (D z : ℝ) := by
      exact_mod_cast hEqZ
    exact le_of_eq hEqR
  calc
    (Nat.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ)
        = (Fintype.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ) := by
          simp [Nat.card_eq_fintype_card]
    _ ≤ (Fintype.card T : ℝ) := by exact_mod_cast hcard_le
    _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := hT_card
    _ ≤ S.sum (fun z : ℂ => (D z : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro z hz
      exact htoNat_le z hz
    _ = divisorMassClosedBall₀ f R := by
      rfl

/-- A finite family of divisor indices contained in a closed ball has cardinality bounded by the
divisor mass of that ball. -/
lemma card_subtype_le_divisorMassClosedBall₀_of_norm_le
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ))} [Fintype s]
    {R : ℝ} (hR : 0 < R) (hs : ∀ p : s, ‖divisorZeroIndex₀_val p.1‖ ≤ R) :
    (Fintype.card s : ℝ) ≤ divisorMassClosedBall₀ f R := by
  let Aball : Type :=
    {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀_val p‖ ≤ R}
  have : Fintype Aball := by
    have : Finite Aball := by
      have : Metric.closedBall (0 : ℂ) R ⊆ (Set.univ : Set ℂ) := by simp
      simpa [Aball] using
        (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := (Set.univ : Set ℂ))
          (B := R) this)
    exact Fintype.ofFinite _
  have hinj : Function.Injective (fun p : s => (⟨p.1, hs p⟩ : Aball)) := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun x : Aball => x.1) hpq
  have hcard_le : Fintype.card s ≤ Fintype.card Aball :=
    Fintype.card_le_of_injective _ hinj
  have hAball : (Nat.card Aball : ℝ) ≤ divisorMassClosedBall₀ f R := by
    simpa [Aball] using card_ball_le_divisorMassClosedBall₀ (f := f) hf hR
  calc
    (Fintype.card s : ℝ) ≤ (Fintype.card Aball : ℝ) := by exact_mod_cast hcard_le
    _ = (Nat.card Aball : ℝ) := by simp [Nat.card_eq_fintype_card]
    _ ≤ divisorMassClosedBall₀ f R := hAball

lemma divisorZeroIndex₀_dyadicShell_upper_bound
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖)
    {k : ℕ} {p : divisorZeroIndex₀ f (Set.univ : Set ℂ)}
    (hp : ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k) :
    ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  exact Real.dyadicShell_upper_bound (r0 := r0) (x := ‖divisorZeroIndex₀_val p‖)
    hr0pos (hr0 p) hp

lemma divisorZeroIndex₀_dyadicShell_lower_bound
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖)
    {k : ℕ} {p : divisorZeroIndex₀ f (Set.univ : Set ℂ)}
    (hp : ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖divisorZeroIndex₀_val p‖ := by
  exact Real.dyadicShell_lower_bound (r0 := r0) (x := ‖divisorZeroIndex₀_val p‖)
    hr0pos (hr0 p) hp

lemma finite_divisorZeroIndex₀_dyadicShell
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖)
    (k : ℕ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
      ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k} : Set _).Finite := by
  have hsub :
      {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
        ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k} ⊆
        {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
          ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} := by
    intro p hp
    exact divisorZeroIndex₀_dyadicShell_upper_bound hr0pos hr0 hp
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
        ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} : Set _).Finite := by
    have :
        Metric.closedBall (0 : ℂ) (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) ⊆
          (Set.univ : Set ℂ) := by
      simp
    simpa using
      (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
        (B := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) this)
  exact hfin.subset hsub

lemma tsum_divisorZeroIndex₀_dyadicShell_inv_rpow_le_geometric_of_growth
    {f : ℂ → ℂ} {ρ τ r0 Cgrow : ℝ}
    (hρ : 0 ≤ ρ) (hτpos : 0 < τ) (hf : Differentiable ℂ f)
    (hCgrow_pos : 0 < Cgrow)
    (hCgrow : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ Cgrow * (1 + ‖z‖) ^ ρ)
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
      r0 ≤ ‖divisorZeroIndex₀_val p‖)
    (k : ℕ) (hk_ge_one : 1 ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) :
    let kfun : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℕ :=
      fun p => ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊
    let S : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := {p | kfun p = k}
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    (∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ) ≤ A * q ^ k + B * qσ ^ k := by
  classical
  intro kfun S Ctrail A B q qσ
  let rk : ℝ := r0 * (2 : ℝ) ^ (k : ℝ)
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have hrk_pos : 0 < rk := mul_pos hr0pos (Real.rpow_pos_of_pos (by norm_num) _)
  have hrk0 : 0 ≤ rk := le_of_lt hrk_pos
  have : Finite S := by
    simpa [S, kfun] using (finite_divisorZeroIndex₀_dyadicShell
      (f := f) hr0pos hr0 k).to_subtype
  have : Fintype S := Fintype.ofFinite S
  have hk_upper : ∀ p : S, ‖divisorZeroIndex₀_val p.1‖ ≤ Rk := by
    intro p
    have hk' : kfun p.1 = k := p.2
    simpa [Rk, kfun] using
      divisorZeroIndex₀_dyadicShell_upper_bound (f := f) hr0pos hr0 hk'
  have hk_lower : ∀ p : S, rk ≤ ‖divisorZeroIndex₀_val p.1‖ := by
    intro p
    have hk' : kfun p.1 = k := p.2
    simpa [rk, kfun] using
      divisorZeroIndex₀_dyadicShell_lower_bound (f := f) hr0pos hr0 hk'
  have htsum_le :
      (∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
        ≤ (Fintype.card S : ℝ) * (rk⁻¹ ^ τ) := by
    exact Real.tsum_inv_rpow_le_card_mul_of_lower_bound
      (a := fun p : S => ‖divisorZeroIndex₀_val p.1‖)
      hrk_pos hτpos (fun _ => norm_nonneg _) hk_lower
  have hmass_le_growth :
      divisorMassClosedBall₀ f Rk
        ≤ (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) := by
    simpa [Ctrail, Rk] using
      (divisorMassClosedBall₀_le_of_growth (f := f) (ρ := ρ) (C := Cgrow) hf hCgrow
        (R := Rk) hk_ge_one)
  have hcard_le_mass :
      (Fintype.card S : ℝ) ≤ divisorMassClosedBall₀ f Rk := by
    have hRk_pos : 0 < Rk := lt_of_lt_of_le (by norm_num) hk_ge_one
    exact card_subtype_le_divisorMassClosedBall₀_of_norm_le (f := f) hf hRk_pos hk_upper
  have htsum' :
      (∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
        ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ) := by
    have hcard_le_growth :
        (Fintype.card S : ℝ) ≤
          (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) :=
      le_trans hcard_le_mass hmass_le_growth
    exact le_trans htsum_le <|
      mul_le_mul_of_nonneg_right hcard_le_growth (Real.rpow_nonneg (inv_nonneg.2 hrk0) τ)
  have hpow_bound :
      (1 + |2 * Rk|) ^ ρ ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
    simpa [Rk] using
      Real.one_add_abs_two_mul_dyadicRadius_rpow_le (r0 := r0) (ρ := ρ) k hr0pos hρ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  simpa [A, B, q, qσ, rk, Ctrail, mul_assoc, mul_left_comm, mul_comm] using
    Real.dyadic_growth_mass_mul_inv_le_geometric
      (C := Cgrow) (L := Real.log 2) (M := (1 + 4 * r0) ^ ρ)
      (X := (1 + |2 * Rk|) ^ ρ)
      (T := ∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
      (Ctrail := Ctrail) (r0 := r0) (ρ := ρ) (τ := τ) (k := k)
      hlog2pos hCgrow_pos.le hr0pos.le hpow_bound
      (by simpa [rk] using htsum')

theorem summable_norm_inv_rpow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ τ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : ρ < τ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by
  rcases hgrowth with ⟨Cgrow, hCgrow_pos, hCgrow⟩
  have hτpos : 0 < τ := lt_of_le_of_lt hρ hτ
  rcases exists_r0_le_norm_divisorZeroIndex₀_val (f := f) hf hnot with ⟨r0, hr0pos, hr0⟩
  have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
  let kfun : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℕ :=
    fun p => ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊
  let S : ℕ → Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    fun k => {p | kfun p = k}
  have hS : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ∃! k : ℕ, p ∈ S k := by
    intro p
    refine ⟨kfun p, ?_, ?_⟩
    · simp [S]
    · intro k hk
      simpa [S] using hk.symm
  have hnonneg : 0 ≤ fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
    intro p
    exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  have hSk_summable : ∀ k : ℕ, Summable fun p : S k => ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
    intro k
    have : Finite (S k) := by
      simpa [S, kfun] using (finite_divisorZeroIndex₀_dyadicShell
        (f := f) hr0pos hr0 k).to_subtype
    exact Summable.of_finite
  have hshell_summable :
      Summable fun k : ℕ => ∑' p : S k, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hq_lt_one : q < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (sub_neg.2 hτ)
    have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hqσ_lt_one : qσ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (by simpa using (neg_neg_of_pos hτpos))
    have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
      summable_geometric_of_lt_one hq_nonneg hq_lt_one
    have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
      summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    rcases Real.exists_nat_le_two_pow (1 / r0) with ⟨k0, hk0⟩
    let A0 : ℝ := A * q ^ k0
    let B0 : ℝ := B * qσ ^ k0
    have hmajor : Summable (fun k : ℕ => A0 * q ^ k + B0 * qσ ^ k) :=
      (hgeom_q.mul_left A0).add (hgeom_qσ.mul_left B0)
    have hshell_summable_shift :
        Summable fun k : ℕ => ∑' p : S (k + k0), ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
      refine hmajor.of_nonneg_of_le
        (fun k => by
          have : ∀ p : S (k + k0), 0 ≤ ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
            intro p; exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
          exact tsum_nonneg this)
        (fun k => by
          let kk : ℕ := k + k0
          let Rk : ℝ := r0 * (2 : ℝ) ^ ((kk : ℝ) + 1)
          have hRk_ge_one : (1 : ℝ) ≤ Rk := by
            have hkk : k0 ≤ kk + 1 := by
              simp [kk, Nat.add_assoc, Nat.add_comm]
            simpa [Rk] using
              Real.one_le_dyadicRadius_succ_of_inv_le_two_pow hr0pos hk0 hkk
          have hmain :
              (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ) ≤ A * q ^ kk + B * qσ ^ kk := by
            simpa [S, kfun, Ctrail, A, B, q, qσ] using
              tsum_divisorZeroIndex₀_dyadicShell_inv_rpow_le_geometric_of_growth
                (f := f) (ρ := ρ) (τ := τ) hρ hτpos hf hCgrow_pos hCgrow hr0pos hr0 kk hRk_ge_one
          have : A * q ^ kk + B * qσ ^ kk = A0 * q ^ k + B0 * qσ ^ k := by
            simpa [A0, B0, kk] using Real.two_geometric_shift_add A B q qσ k k0
          simpa [kk] using (hmain.trans_eq this)
        )
    exact (summable_nat_add_iff k0).1 hshell_summable_shift
  have hpart :=
    (summable_partition (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) hnonneg (s := S) hS)
  exact (hpart.2 ⟨hSk_summable, hshell_summable⟩)

/-- Natural-power form of the divisor summability theorem. -/
theorem summable_norm_inv_pow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  have hτ : ρ < (Nat.floor ρ + 1 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (a := ρ))
  have hs :=
    summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ)
      (τ := (Nat.floor ρ + 1 : ℝ)) hρ hτ hf hnot hgrowth
  exact hs.congr fun p => by
    have hcast : ((Nat.floor ρ : ℝ) + 1) = ((Nat.floor ρ + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hcast, Real.rpow_natCast]

end Complex.Hadamard
end Erdos970
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_HadamardSupport
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970.Complex.Hadamard
open _root_.Complex

lemma divisorZeroIndex₀Val_mem_divisor_support {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    MeromorphicOn.divisor f U (divisorZeroIndex₀Val p) ≠ 0 :=
  divisorZeroIndex₀_val_mem_divisor_support p

end Erdos970.Complex.Hadamard
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_MellinConvergentTopIndicator
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section AnalyticAssemblyScope

open scoped BigOperators Topology

section

open _root_.Filter _root_.Set _root_.MeasureTheory
open scoped Topology

namespace WeightedTorusJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma mellinConvergent_top_indicator (P : WeakFEPair E) (s : ℂ) :
    MellinConvergent ((Ioi 1).indicator (fun t ↦ P.f t - P.f₀)) s := by
  have hi : MellinConvergent P.f_modif s :=
    (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  change IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • P.f_modif t) (Ioi 0) at hi
  unfold MellinConvergent
  convert hi.indicator (t := Ioi 1) measurableSet_Ioi using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  by_cases ht : 1 < t
  · simp [WeakFEPair.f_modif, ht, notMem_Ioo_of_ge ht.le]
  · simp [ht]

lemma f_modif_eq_top_add_inv (P : WeakFEPair E) {t : ℝ} (ht : 0 < t) :
    P.f_modif t = (Ioi 1).indicator (fun x ↦ P.f x - P.f₀) t +
      P.ε • ((t : ℂ) ^ (-P.k : ℂ) •
        (Ioi 1).indicator (fun x ↦ P.g x - P.g₀) t⁻¹) := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr h
    have heq := P.hf_modif_FE t⁻¹ (inv_pos.mpr ht)
    rw [one_div, inv_inv] at heq
    rw [Set.indicator_of_notMem (show t ∉ Ioi 1 from not_lt.mpr h.le), zero_add,
      Set.indicator_of_mem (show t⁻¹ ∈ Ioi 1 from hinv), heq]
    simp only [WeakFEPair.g_modif, Pi.add_apply,
      Set.indicator_of_mem (show t⁻¹ ∈ Ioi 1 from hinv),
      Set.indicator_of_notMem (notMem_Ioo_of_ge hinv.le),
      add_zero, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, Complex.ofReal_cpow ht.le,
      Complex.ofReal_neg, mul_smul]
  · simp [WeakFEPair.f_modif]
  · have hinv : ¬1 < t⁻¹ := not_lt.mpr ((inv_le_one₀ ht).mpr h.le)
    simp [WeakFEPair.f_modif, h, notMem_Ioo_of_ge h.le, hinv]

lemma mellin_top_indicator_eq (f : ℝ → E) (s : ℂ) :
    mellin ((Ioi 1).indicator f) s =
      ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) • f t := by
  simp only [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]

lemma Lambda_zero_eq_top_integrals (P : WeakFEPair E) (s : ℂ) :
    P.Λ₀ s = (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) • (P.f t - P.f₀)) +
      P.ε • (∫ t : ℝ in Ioi 1, (t : ℂ) ^ ((P.k : ℂ) - s - 1) • (P.g t - P.g₀)) := by
  let F := (Ioi 1).indicator (fun t ↦ P.f t - P.f₀)
  let G := (Ioi 1).indicator (fun t ↦ P.g t - P.g₀)
  have hF : MellinConvergent F s := mellinConvergent_top_indicator P s
  have hG : MellinConvergent G (P.k - s) := mellinConvergent_top_indicator P.symm _
  have hInv : MellinConvergent (fun t ↦ G t⁻¹) (s - P.k) := by
    have hdiv : (s - (P.k : ℂ)) / ((-1 : ℝ) : ℂ) = (P.k : ℂ) - s := by
      simp only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one, neg_sub]
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (f := G) (s := s - P.k)
        (a := -1) (by norm_num)).mpr (hdiv.symm ▸ hG)
  have hSecond : MellinConvergent
      (fun t : ℝ ↦ P.ε • ((t : ℂ) ^ (-P.k : ℂ) • G t⁻¹)) s := by
    apply MellinConvergent.const_smul
    apply MellinConvergent.cpow_smul.mpr
    simpa only [sub_eq_add_neg] using hInv
  calc
    P.Λ₀ s = mellin (fun t : ℝ ↦ F t + P.ε • ((t : ℂ) ^ (-P.k : ℂ) • G t⁻¹)) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact congrArg (fun v : E ↦ (t : ℂ) ^ (s - 1) • v) (f_modif_eq_top_add_inv P ht)
    _ = mellin F s + mellin (fun t : ℝ ↦ P.ε • ((t : ℂ) ^ (-P.k : ℂ) • G t⁻¹)) s :=
      (hasMellin_add hF hSecond).2
    _ = mellin F s + P.ε • mellin G (P.k - s) := by
      rw [mellin_const_smul, mellin_cpow_smul, mellin_comp_inv]
      congr 3
      ring
    _ = _ := by rw [mellin_top_indicator_eq, mellin_top_indicator_eq]

lemma norm_top_integral_le (f : ℝ → E) (s : ℂ) :
    ‖∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) • f t‖ ≤
      ∫ t : ℝ in Ioi 1, t ^ (s.re - 1) * ‖f t‖ := by
  apply le_trans (norm_integral_le_integral_norm _)
  apply le_of_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht),
    Complex.sub_re, Complex.one_re]

theorem norm_Lambda_zero_le_top_integrals (P : WeakFEPair E) (s : ℂ) :
    ‖P.Λ₀ s‖ ≤ (∫ t : ℝ in Ioi 1, t ^ (s.re - 1) * ‖P.f t - P.f₀‖) +
      ‖P.ε‖ * (∫ t : ℝ in Ioi 1, t ^ (P.k - s.re - 1) * ‖P.g t - P.g₀‖) := by
  rw [Lambda_zero_eq_top_integrals]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul]
  apply add_le_add (norm_top_integral_le _ s)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa using (norm_top_integral_le (fun t ↦ P.g t - P.g₀) (P.k - s))

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.Real _root_.Set _root_.MeasureTheory

theorem exponential_moment_integrable {p R : ℝ} (hp : 0 < p) (hR : 0 ≤ R) :
    IntegrableOn (fun t : ℝ => t ^ R * exp (-p * t)) (Ioi 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := R) (p := 1)
    (by linarith) zero_lt_one hp
  simp only [rpow_one] at h
  exact h.mono_set (Ioi_subset_Ioi (by norm_num))

theorem exponential_moment_pointwise {p R t : ℝ}
    (hp : 0 < p) (hR : 0 ≤ R) (ht : 1 ≤ t) :
    t ^ R * exp (-p * t) ≤
      exp ((R + 1) * log (2 * (R + 1) / p)) * exp (-(p / 2) * t) := by
  have hr : 0 < R + 1 := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ha : 0 < 2 * (R + 1) / p := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht0 ha)
  rw [Real.log_div ht0.ne' ha.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hr.le
  have heq : (R + 1) * (t / (2 * (R + 1) / p) - 1) = p * t / 2 - (R + 1) := by
    field_simp
  rw [heq] at hmul
  have htlog := Real.log_nonneg ht
  rw [Real.rpow_def_of_pos ht0, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem exponential_moment_le {p R : ℝ} (hp : 0 < p) (hR : 0 ≤ R) :
    (∫ t : ℝ in Ioi 1, t ^ R * exp (-p * t)) ≤
      exp ((R + 1) * log (2 * (R + 1) / p)) * (2 / p) := by
  have hp2 : -(p / 2) < 0 := by linarith
  have hi := (integrableOn_exp_mul_Ioi hp2 1).const_mul
    (exp ((R + 1) * log (2 * (R + 1) / p)))
  calc
    _ ≤ ∫ t : ℝ in Ioi 1,
        exp ((R + 1) * log (2 * (R + 1) / p)) * exp (-(p / 2) * t) :=
      setIntegral_mono_on (exponential_moment_integrable hp hR) hi measurableSet_Ioi
        (fun t ht => exponential_moment_pointwise hp hR ht.le)
    _ = exp ((R + 1) * log (2 * (R + 1) / p)) *
        (exp (-(p / 2)) * (2 / p)) := by
      rw [integral_const_mul, integral_exp_mul_Ioi hp2]
      congr 1
      simp only [mul_one]
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
      calc
        _ ≤ 1 * (2 / p) := mul_le_mul_of_nonneg_right
          (Real.exp_le_one_iff.mpr hp2.le) (by positivity)
        _ = _ := one_mul _

theorem mul_log_le_three_halves {u : ℝ} (hu : 1 ≤ u) :
    u * log u ≤ 2 * u ^ (3 / 2 : ℝ) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hlog := Real.log_le_rpow_div hu0.le (by norm_num : 0 < (1 / 2 : ℝ))
  have hmul := mul_le_mul_of_nonneg_left hlog hu0.le
  have heq : u * u ^ (1 / 2 : ℝ) = u ^ (3 / 2 : ℝ) := by
    calc
      _ = u ^ ((1 : ℝ) + 1 / 2) := by rw [Real.rpow_add hu0, Real.rpow_one]
      _ = _ := by norm_num
  nlinarith

theorem exponential_moment_growth {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R →
      (∫ t : ℝ in Ioi 1, t ^ R * exp (-p * t)) ≤
        exp (C * (1 + R) ^ (3 / 2 : ℝ)) := by
  refine ⟨2 * |log (2 / p)| + 2, by positivity, fun R hR => ?_⟩
  have hr : 0 < R + 1 := by positivity
  have hp2 : 0 < 2 / p := by positivity
  have hpow : R + 1 ≤ (R + 1) ^ (3 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ R + 1)
      (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hpow1 : 1 ≤ (R + 1) ^ (3 / 2 : ℝ) := by
    exact one_le_rpow (by linarith) (by norm_num)
  have hlog := mul_log_le_three_halves (by linarith : 1 ≤ R + 1)
  have hA := le_abs_self (log (2 / p))
  have hAu := mul_le_mul_of_nonneg_left hA hr.le
  have hA1 := mul_le_mul_of_nonneg_left hpow1 (abs_nonneg (log (2 / p)))
  have hApow := mul_le_mul_of_nonneg_left hpow (abs_nonneg (log (2 / p)))
  calc
    _ ≤ exp ((R + 1) * log (2 * (R + 1) / p)) * (2 / p) :=
      exponential_moment_le hp hR
    _ = exp ((R + 1) * log (2 * (R + 1) / p) + log (2 / p)) := by
      rw [Real.exp_add, Real.exp_log hp2]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [show 2 * (R + 1) / p = (2 / p) * (R + 1) by ring,
        Real.log_mul hp2.ne' hr.ne', show 1 + R = R + 1 by ring]
      nlinarith

theorem log_one_add_le_log_two_add {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x)
    (h : b ≤ exp x) : log (1 + b) ≤ log 2 + x := by
  calc
    _ ≤ log (2 * exp x) := Real.log_le_log (by positivity)
      (by linarith [Real.one_le_exp_iff.mpr hx])
    _ = _ := by rw [Real.log_mul (by norm_num) (exp_pos _).ne', Real.log_exp]

theorem log_norm_growth_of_norm_growth {F : ℂ → ℂ}
    (hF : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖F s‖ ≤ exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ))) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ,
      log (1 + ‖F s‖) ≤ D * (1 + ‖s‖) ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hF⟩ := hF
  refine ⟨C + log 2, by positivity, fun s => ?_⟩
  have hpow1 : 1 ≤ (1 + ‖s‖) ^ (3 / 2 : ℝ) :=
    one_le_rpow (le_add_of_nonneg_right (norm_nonneg _)) (by norm_num)
  have hlog2 : 0 ≤ log 2 := by positivity
  have hlog := log_one_add_le_log_two_add (norm_nonneg _) (by positivity) (hF s)
  have hmul := mul_le_mul_of_nonneg_left hpow1 hlog2
  nlinarith

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.Filter _root_.Set _root_.MeasureTheory _root_.Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
lemma weighted_norm_integral_le_moment (f : ℝ → E) {p C a R : ℝ}
    (hp : 0 < p) (hR : 0 ≤ R) (ha : a ≤ R)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * exp (-p * t)) :
    (∫ t : ℝ in Ioi 1, t ^ a * ‖f t‖) ≤
      C * (∫ t : ℝ in Ioi 1, t ^ R * exp (-p * t)) := by
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (rpow_nonneg (zero_lt_one.trans ht).le _) (norm_nonneg _)
  · exact (exponential_moment_integrable hp hR).const_mul C
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      _ ≤ t ^ R * (C * exp (-p * t)) :=
        mul_le_mul (rpow_le_rpow_of_exponent_le ht.le ha) (hf t ht.le)
          (norm_nonneg _) (rpow_nonneg (zero_lt_one.trans ht).le _)
      _ = _ := by ring

theorem norm_Lambda_zero_growth_of_exp_bounds (P : WeakFEPair E)
    (hf : ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 1 ≤ t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 1 ≤ t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t)) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ,
      ‖P.Λ₀ s‖ ≤ exp (B * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨pf, hpf, Cf, hCf, hf⟩ := hf
  obtain ⟨pg, hpg, Cg, hCg, hg⟩ := hg
  obtain ⟨Ef, hEf, hEf_bound⟩ := exponential_moment_growth hpf
  obtain ⟨Eg, hEg, hEg_bound⟩ := exponential_moment_growth hpg
  let D := Ef + Eg
  let K := (2 + |P.k|) ^ (3 / 2 : ℝ)
  let A := Cf + ‖P.ε‖ * Cg
  have hD : 0 < D := by dsimp [D] <;> positivity
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hA : 0 < A := by dsimp [A] <;> positivity
  refine ⟨A + D * K, by positivity, ?_⟩
  intro s
  let R := 1 + |P.k| + ‖s‖
  let r := (1 + ‖s‖) ^ (3 / 2 : ℝ)
  have hR : 0 ≤ R := by dsimp [R] <;> positivity
  have hr : 0 ≤ r := by dsimp [r] <;> positivity
  have hr1 : 1 ≤ r := one_le_rpow (by simp) (by norm_num)
  have hfexp : s.re - 1 ≤ R := by
    have := Complex.re_le_norm s
    dsimp [R]
    linarith [abs_nonneg P.k]
  have hgexp : P.k - s.re - 1 ≤ R := by
    have := (neg_le_abs s.re).trans (Complex.abs_re_le_norm s)
    dsimp [R]
    linarith [le_abs_self P.k]
  have hweight : (1 + R) ^ (3 / 2 : ℝ) ≤ K * r := by
    calc
      _ ≤ ((2 + |P.k|) * (1 + ‖s‖)) ^ (3 / 2 : ℝ) := by
        apply rpow_le_rpow (by positivity) _ (by norm_num)
        dsimp [R]
        nlinarith [abs_nonneg P.k, norm_nonneg s]
      _ = _ := by rw [mul_rpow (by positivity) (by positivity)]
  have hEfm : Ef * (1 + R) ^ (3 / 2 : ℝ) ≤ D * K * r := by
    have h1 := mul_le_mul_of_nonneg_left hweight hEf.le
    have h2 := mul_le_mul_of_nonneg_right (show Ef ≤ D by dsimp [D] <;> linarith)
      (mul_nonneg hK.le hr)
    nlinarith
  have hEgm : Eg * (1 + R) ^ (3 / 2 : ℝ) ≤ D * K * r := by
    have h1 := mul_le_mul_of_nonneg_left hweight hEg.le
    have h2 := mul_le_mul_of_nonneg_right (show Eg ≤ D by dsimp [D] <;> linarith)
      (mul_nonneg hK.le hr)
    nlinarith
  have hfint : (∫ t : ℝ in Ioi 1, t ^ (s.re - 1) * ‖P.f t - P.f₀‖) ≤
      Cf * exp (D * K * r) := by
    apply (weighted_norm_integral_le_moment _ hpf hR hfexp hf).trans
    exact mul_le_mul_of_nonneg_left
      ((hEf_bound R hR).trans (exp_le_exp.mpr hEfm)) hCf.le
  have hgint : (∫ t : ℝ in Ioi 1, t ^ (P.k - s.re - 1) * ‖P.g t - P.g₀‖) ≤
      Cg * exp (D * K * r) := by
    apply (weighted_norm_integral_le_moment _ hpg hR hgexp hg).trans
    exact mul_le_mul_of_nonneg_left
      ((hEg_bound R hR).trans (exp_le_exp.mpr hEgm)) hCg.le
  have hAexp : A ≤ exp (A * r) := by
    have h1 := mul_le_mul_of_nonneg_left hr1 hA.le
    exact (by linarith : A ≤ A * r + 1).trans (add_one_le_exp _)
  calc
    ‖P.Λ₀ s‖ ≤ Cf * exp (D * K * r) + ‖P.ε‖ * (Cg * exp (D * K * r)) :=
      (norm_Lambda_zero_le_top_integrals P s).trans
        (add_le_add hfint (mul_le_mul_of_nonneg_left hgint (norm_nonneg _)))
    _ = A * exp (D * K * r) := by dsimp [A] <;> ring
    _ ≤ exp (A * r) * exp (D * K * r) :=
      mul_le_mul_of_nonneg_right hAexp (exp_nonneg _)
    _ = _ := by rw [← exp_add]; congr 1; dsimp [r] <;> ring

end WeightedTorusJets

open _root_.Filter _root_.Set _root_.Asymptotics

namespace WeightedTorusJets

theorem exists_global_exp_bound {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {p : ℝ} (hf : ContinuousOn f (Ici 1))
    (hdecay : f =O[atTop] (fun t : ℝ => Real.exp (-p * t))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨A, _, hA⟩ := hdecay.exists_pos
  obtain ⟨T, hT⟩ := eventually_atTop.mp hA.bound
  have hcompact : ContinuousOn (fun t => ‖f t‖ / Real.exp (-p * t))
      (Icc 1 (max 1 T)) := by
    apply (hf.mono fun _ ht => ht.1).norm.div
    · fun_prop
    · exact fun _ _ => Real.exp_ne_zero _
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcompact
  refine ⟨max 1 (max A B), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  by_cases hlarge : T ≤ t
  · calc
      ‖f t‖ ≤ A * Real.exp (-p * t) := by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hT t hlarge
      _ ≤ max 1 (max A B) * Real.exp (-p * t) :=
        mul_le_mul_of_nonneg_right ((le_max_left A B).trans (le_max_right _ _))
          (Real.exp_pos _).le
  · have hsmall := hB t ⟨ht, (le_of_not_ge hlarge).trans (le_max_right _ _)⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
      at hsmall
    calc
      ‖f t‖ ≤ B * Real.exp (-p * t) := (div_le_iff₀ (Real.exp_pos _)).mp hsmall
      _ ≤ max 1 (max A B) * Real.exp (-p * t) :=
        mul_le_mul_of_nonneg_right ((le_max_right A B).trans (le_max_right _ _))
          (Real.exp_pos _).le

theorem exists_evenKernel_sub_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖HurwitzZeta.evenKernel a t - (if a = 0 then 1 else 0)‖ ≤
        C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub a
  refine ⟨p, hp, exists_global_exp_bound ?_ hdecay⟩
  exact ((HurwitzZeta.continuousOn_evenKernel a).sub continuousOn_const).mono
    fun t ht => (show (0 : ℝ) < t from lt_of_lt_of_le zero_lt_one ht)

theorem exists_cosKernel_sub_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖HurwitzZeta.cosKernel a t - 1‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_cosKernel_sub a
  refine ⟨p, hp, exists_global_exp_bound ?_ hdecay⟩
  exact ((HurwitzZeta.continuousOn_cosKernel a).sub continuousOn_const).mono
    fun t ht => (show (0 : ℝ) < t from lt_of_lt_of_le zero_lt_one ht)

theorem exists_oddKernel_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖HurwitzZeta.oddKernel a t‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_oddKernel a
  refine ⟨p, hp, exists_global_exp_bound ?_ hdecay⟩
  exact (HurwitzZeta.continuousOn_oddKernel a).mono
    fun t ht => (show (0 : ℝ) < t from lt_of_lt_of_le zero_lt_one ht)

theorem exists_sinKernel_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖HurwitzZeta.sinKernel a t‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_sinKernel a
  refine ⟨p, hp, exists_global_exp_bound ?_ hdecay⟩
  exact (HurwitzZeta.continuousOn_sinKernel a).mono
    fun t ht => (show (0 : ℝ) < t from lt_of_lt_of_le zero_lt_one ht)

theorem exists_hurwitzEvenFEPair_f_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(HurwitzZeta.hurwitzEvenFEPair a).f t - (HurwitzZeta.hurwitzEvenFEPair a).f₀‖ ≤
        C * Real.exp (-p * t) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := exists_evenKernel_sub_exp_bound a
  refine ⟨p, hp, C, hC, fun t ht => ?_⟩
  by_cases ha : a = 0 <;>
    simpa [HurwitzZeta.hurwitzEvenFEPair, ha, ← Complex.ofReal_one,
      ← Complex.ofReal_sub] using hbound t ht

theorem exists_hurwitzEvenFEPair_g_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(HurwitzZeta.hurwitzEvenFEPair a).g t - (HurwitzZeta.hurwitzEvenFEPair a).g₀‖ ≤
        C * Real.exp (-p * t) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := exists_cosKernel_sub_exp_bound a
  refine ⟨p, hp, C, hC, fun t ht => ?_⟩
  simpa [HurwitzZeta.hurwitzEvenFEPair, ← Complex.ofReal_one,
    ← Complex.ofReal_sub] using hbound t ht

theorem exists_hurwitzOddFEPair_f_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(HurwitzZeta.hurwitzOddFEPair a).f t - (HurwitzZeta.hurwitzOddFEPair a).f₀‖ ≤
        C * Real.exp (-p * t) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := exists_oddKernel_exp_bound a
  refine ⟨p, hp, C, hC, fun t ht => ?_⟩
  simpa [HurwitzZeta.hurwitzOddFEPair] using hbound t ht

theorem exists_hurwitzOddFEPair_g_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(HurwitzZeta.hurwitzOddFEPair a).g t - (HurwitzZeta.hurwitzOddFEPair a).g₀‖ ≤
        C * Real.exp (-p * t) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := exists_sinKernel_exp_bound a
  refine ⟨p, hp, C, hC, fun t ht => ?_⟩
  simpa [HurwitzZeta.hurwitzOddFEPair] using hbound t ht



theorem norm_growth_half_shift {F : ℂ → ℂ}
    (hF : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖F s‖ ≤ Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)))
    {b : ℂ} (hb : ‖b‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖F ((s + b) / 2) / 2‖ ≤ Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hF⟩ := hF
  refine ⟨4 * C, by positivity, fun s => ?_⟩
  have harg : 1 + ‖(s + b) / 2‖ ≤ 2 * (1 + ‖s‖) := by
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le s b
    nlinarith [norm_nonneg s]
  have hpow : (1 + ‖(s + b) / 2‖) ^ (3 / 2 : ℝ) ≤
      4 * (1 + ‖s‖) ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ (2 * (1 + ‖s‖)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) harg (by norm_num)
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (1 + ‖s‖) ^ (3 / 2 : ℝ) :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          (2 : ℝ) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := by norm_num
  calc
    _ ≤ ‖F ((s + b) / 2)‖ := by
      rw [norm_div, Complex.norm_ofNat]
      exact div_le_self (norm_nonneg _) (by norm_num)
    _ ≤ Real.exp (C * (1 + ‖(s + b) / 2‖) ^ (3 / 2 : ℝ)) := hF _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hpow hC.le]

theorem norm_completedHurwitzZetaEven_zero_growth_of_Lambda_zero_growth
    (a : UnitAddCircle)
    (hF : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖(HurwitzZeta.hurwitzEvenFEPair a).Λ₀ s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaEven₀ a s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  simpa [HurwitzZeta.completedHurwitzZetaEven₀] using
    norm_growth_half_shift hF (b := 0) (by simp)

theorem norm_completedHurwitzZetaOdd_growth_of_Lambda_zero_growth
    (a : UnitAddCircle)
    (hF : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖(HurwitzZeta.hurwitzOddFEPair a).Λ₀ s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaOdd a s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  have hΛ : (HurwitzZeta.hurwitzOddFEPair a).Λ =
      (HurwitzZeta.hurwitzOddFEPair a).Λ₀ := by
    ext s
    simp [WeakFEPair.Λ, HurwitzZeta.hurwitzOddFEPair]
  simpa only [HurwitzZeta.completedHurwitzZetaOdd, hΛ] using
    norm_growth_half_shift hF (b := 1) (by simp)



theorem exists_completedHurwitzZetaEven_zero_growth (a : UnitAddCircle) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaEven₀ a s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) :=
  norm_completedHurwitzZetaEven_zero_growth_of_Lambda_zero_growth a
    (norm_Lambda_zero_growth_of_exp_bounds (HurwitzZeta.hurwitzEvenFEPair a)
      (exists_hurwitzEvenFEPair_f_exp_bound a) (exists_hurwitzEvenFEPair_g_exp_bound a))

theorem exists_completedHurwitzZetaOdd_growth (a : UnitAddCircle) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaOdd a s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) :=
  norm_completedHurwitzZetaOdd_growth_of_Lambda_zero_growth a
    (norm_Lambda_zero_growth_of_exp_bounds (HurwitzZeta.hurwitzOddFEPair a)
      (exists_hurwitzOddFEPair_f_exp_bound a) (exists_hurwitzOddFEPair_g_exp_bound a))

end WeightedTorusJets

end
end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ConductorCompletedL
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section AnalyticAssemblyScope
open scoped BigOperators Topology
section
open _root_.Filter _root_.Set _root_.MeasureTheory
open scoped Topology
open _root_.Filter _root_.Set _root_.Asymptotics
namespace WeightedTorusJets

open _root_.Complex _root_.Erdos970.Complex DirichletCharacter

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
theorem gammaFactor_ne_zero_of_re_pos (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [hodd.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, one_re]
    linarith

theorem completedL_eq_mul_gammaFactor (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) :
    completedLFunction χ s = LFunction χ s * gammaFactor χ s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [LFunction_eq_completed_div_gammaFactor χ s (.inl hs0)]
  exact (div_mul_cancel₀ _ (gammaFactor_ne_zero_of_re_pos χ hs)).symm

theorem completedL_ne_zero_of_one_le_re (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : completedLFunction χ s ≠ 0 := by
  have hs0 : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
  rw [completedL_eq_mul_gammaFactor χ hs0]
  exact mul_ne_zero (LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs)
    (gammaFactor_ne_zero_of_re_pos χ hs0)

theorem conductorCompletedL_zero_iff (χ : DirichletCharacter ℂ q) (s : ℂ) :
    conductorCompletedL χ s = 0 ↔ completedLFunction χ s = 0 := by
  simp [conductorCompletedL, Nat.cast_ne_zero.mpr (NeZero.ne q)]

theorem differentiable_conductorCompletedL (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Differentiable ℂ (conductorCompletedL χ) := by
  apply Differentiable.mul
  · exact (differentiable_id.div_const (2 : ℂ)).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  · exact differentiable_completedLFunction hχ

theorem completedL_zero_re_mem_Ioo (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {ρ : ℂ}
    (hρ : completedLFunction χ ρ = 0) : ρ.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have hinv : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.IsPrimitive, conductor_inv] using hχ
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  constructor
  · by_contra! hn
    have hz : completedLFunction χ⁻¹ (1 - ρ) = 0 := by
      rw [hinv.completedLFunction_one_sub, inv_inv, hρ, mul_zero]
    exact completedL_ne_zero_of_one_le_re χ⁻¹ hinv1 (by simp only [sub_re, one_re] <;> linarith) hz
  · by_contra! hn
    exact completedL_ne_zero_of_one_le_re χ hχ1 hn hρ

theorem completedL_eq_poleFree (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    completedLFunction χ s = ZMod.completedLFunction₀ χ s := by
  have hq : q ≠ 1 := hχ ∘ level_one' _
  simp [completedLFunction, ZMod.completedLFunction_eq, χ.map_zero' hq,
    χ.sum_eq_zero_of_ne_one hχ]

theorem conductorCompletedL_eq_hurwitzSum (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) :
    conductorCompletedL χ s = (q : ℂ) ^ (-s / 2) *
      ((∑ j : ZMod q, χ j * HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s) +
       ∑ j : ZMod q, χ j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s) := by
  rw [conductorCompletedL, completedL_eq_poleFree χ hχ, ZMod.completedLFunction₀]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  calc
    _ = ((q : ℂ) ^ (s / 2) * (q : ℂ) ^ (-s)) *
      ((∑ j : ZMod q, χ j * HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s) +
       ∑ j : ZMod q, χ j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hq]
      congr 2
      ring

theorem norm_conductor_power_le (s : ℂ) :
    ‖(q : ℂ) ^ (-s / 2)‖ ≤ Real.exp (Real.log (q : ℝ) * ‖s‖ / 2) := by
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (NeZero.pos q)
  change ‖((q : ℝ) : ℂ) ^ (-s / 2)‖ ≤ _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq, Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  simp only [Complex.div_ofNat_re, neg_re]
  have hreal : -s.re ≤ ‖s‖ := (neg_le_abs s.re).trans (Complex.abs_re_le_norm s)
  have := mul_le_mul_of_nonneg_left hreal (Real.log_nonneg hq1)
  nlinarith

theorem norm_conductorCompletedL_le_hurwitzSum (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) :
    ‖conductorCompletedL χ s‖ ≤ Real.exp (Real.log (q : ℝ) * ‖s‖ / 2) *
      ((∑ j : ZMod q, ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖) +
       ∑ j : ZMod q, ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖) := by
  have hsum : ∀ f : ZMod q → ℂ, ‖∑ j, χ j * f j‖ ≤ ∑ j, ‖f j‖ := by
    intro f
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)
  rw [conductorCompletedL_eq_hurwitzSum χ hχ s, norm_mul]
  apply mul_le_mul (norm_conductor_power_le s)
    ((norm_add_le _ _).trans (add_le_add (hsum _) (hsum _))) (norm_nonneg _)
    (Real.exp_nonneg _)

omit [NeZero q] in
theorem finite_uniform_exp_bound {ι : Type*} [Finite ι] (f : ι → ℂ → ℂ)
    (r : ℂ → ℝ) (hr : ∀ z, 0 ≤ r z)
    (hf : ∀ i, ∃ C > 0, ∀ z, ‖f i z‖ ≤ Real.exp (C * r z)) :
    ∃ C > 0, ∀ i z, ‖f i z‖ ≤ Real.exp (C * r z) := by
  choose c _ hc using hf
  obtain ⟨B, hB⟩ := (Set.finite_range c).bddAbove
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun i z => ?_⟩
  exact (hc i z).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    ((hB (Set.mem_range_self i)).trans (le_max_left _ _)) (hr z)))

theorem conductorCompletedL_growth_of_hurwitz (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1)
    (he : ∀ j : ZMod q, ∃ C > 0, ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)))
    (ho : ∀ j : ZMod q, ∃ C > 0, ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ))) :
    ∃ C > 0, ∀ s : ℂ, ‖conductorCompletedL χ s‖ ≤
      Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  classical
  let r : ℂ → ℝ := fun s => (1 + ‖s‖) ^ (3 / 2 : ℝ)
  have hr : ∀ s, 0 ≤ r s := fun s => Real.rpow_nonneg (by positivity) _
  obtain ⟨E, hE, he⟩ := finite_uniform_exp_bound _ r hr he
  obtain ⟨O, hO, ho⟩ := finite_uniform_exp_bound _ r hr ho
  let B := max E O
  have hB : 0 < B := lt_of_lt_of_le hE (le_max_left _ _)
  have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (NeZero.pos q)
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  refine ⟨Real.log (q : ℝ) / 2 + B + 2 * q, by positivity, fun s => ?_⟩
  have hr1 : 1 ≤ r s := Real.one_le_rpow (by simp) (by norm_num)
  have hrs : ‖s‖ ≤ r s := (by linarith : ‖s‖ ≤ 1 + ‖s‖).trans
    (Real.self_le_rpow_of_one_le (by simp) (by norm_num))
  have he' : ∀ j : ZMod q,
      ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤
        Real.exp (B * r s) := fun j => (he j s).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (hr s)))
  have ho' : ∀ j : ZMod q,
      ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤
        Real.exp (B * r s) := fun j => (ho j s).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (hr s)))
  have hsum :
      ((∑ j : ZMod q, ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖) +
       ∑ j : ZMod q, ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖) ≤
      (2 * q) * Real.exp (B * r s) := by
    have h1 := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (ZMod q))) => he' j)
    have h2 := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (ZMod q))) => ho' j)
    simpa [Finset.sum_const, ZMod.card, nsmul_eq_mul, two_mul, add_mul] using add_le_add h1 h2
  have hcard : (2 * q : ℝ) ≤ Real.exp ((2 * q : ℝ) * r s) := by
    have h1 : (2 * q : ℝ) ≤ (2 * q : ℝ) * r s :=
      le_mul_of_one_le_right (by positivity) hr1
    exact h1.trans ((by linarith : (2 * q : ℝ) * r s ≤ (2 * q : ℝ) * r s + 1).trans
      (Real.add_one_le_exp _))
  calc
    ‖conductorCompletedL χ s‖ ≤ Real.exp (Real.log (q : ℝ) * ‖s‖ / 2) *
        ((2 * q) * Real.exp (B * r s)) :=
      (norm_conductorCompletedL_le_hurwitzSum χ hχ s).trans
        (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _))
    _ ≤ Real.exp ((Real.log (q : ℝ) / 2) * r s) *
        (Real.exp ((2 * q : ℝ) * r s) * Real.exp (B * r s)) := by
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hrs hlog]
      · exact mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      · positivity
      · positivity
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [r] <;> ring

theorem conductorCompletedL_ne_zero_at_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) : conductorCompletedL χ 0 ≠ 0 := by
  intro hzero
  have hstrip := completedL_zero_re_mem_Ioo χ hχ hχ1
    ((conductorCompletedL_zero_iff χ 0).mp hzero)
  norm_num at hstrip

end WeightedTorusJets

namespace WeightedTorusJets

theorem conductorCompletedL_norm_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C > 0, ∀ s : ℂ, ‖conductorCompletedL χ s‖ ≤
      Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) :=
  conductorCompletedL_growth_of_hurwitz χ hχ
    (fun j => exists_completedHurwitzZetaEven_zero_growth (ZMod.toAddCircle j))
    (fun j => exists_completedHurwitzZetaOdd_growth (ZMod.toAddCircle j))

theorem conductorCompletedL_log_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C > 0, ∀ s : ℂ, Real.log (1 + ‖conductorCompletedL χ s‖) ≤
      C * (1 + ‖s‖) ^ (3 / 2 : ℝ) :=
  log_norm_growth_of_norm_growth (conductorCompletedL_norm_growth χ hχ)



open _root_.Erdos970.Complex.Hadamard

variable {q : ℕ} [NeZero q]

theorem conductorCompletedL_zeroIndex_vanishes (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1)
    (p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ)) :
    conductorCompletedL χ (divisorZeroIndex₀Val p) = 0 := by
  by_contra hnonzero
  have ha : AnalyticOnNhd ℂ (conductorCompletedL χ) Set.univ :=
    fun z _ => (differentiable_conductorCompletedL χ hχ).analyticAt z
  have hdiv : MeromorphicOn.divisor (conductorCompletedL χ) Set.univ
      (divisorZeroIndex₀Val p) = 0 := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ _),
      (ha _ (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hnonzero]
    simp
  exact divisorZeroIndex₀Val_mem_divisor_support p hdiv

theorem conductorCompletedL_zeroIndex_summable_inv_sq (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (2 : ℕ)) := by
  have hfloor : Nat.floor (3 / 2 : ℝ) = 1 := by
    apply (Nat.floor_eq_iff (by norm_num)).mpr
    norm_num
  simpa [hfloor] using summable_norm_inv_pow_divisorZeroIndex₀_of_growth
    (f := conductorCompletedL χ) (ρ := (3 / 2 : ℝ)) (by norm_num)
    (differentiable_conductorCompletedL χ hχ)
    ⟨0, conductorCompletedL_ne_zero_at_zero χ hp hχ⟩
    (conductorCompletedL_log_growth χ hχ)

theorem conductorCompletedL_logDeriv_hasSum_jb247_oai (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ B : ℂ, ∀ s : ℂ, conductorCompletedL χ s ≠ 0 →
      HasSum (fun p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ) =>
        1 / (s - divisorZeroIndex₀Val p) + 1 / divisorZeroIndex₀Val p)
        (logDeriv (conductorCompletedL χ) s - B) := by
  obtain ⟨P, hP, hfac⟩ := conductorCompletedL_hadamard_factorization_jb247 χ hp hχ
  have hsum := conductorCompletedL_zeroIndex_summable_inv_sq χ hp hχ
  refine ⟨P.coeff 1, fun s hs => ?_⟩
  have hsindex : ∀ p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ),
      s ≠ divisorZeroIndex₀Val p := by
    intro p hsp
    exact hs (hsp ▸ conductorCompletedL_zeroIndex_vanishes χ hχ p)
  have hprod : divisorCanonicalProduct 1 (conductorCompletedL χ) (Set.univ : Set ℂ) s ≠ 0 :=
    divisorCanonicalProduct_ne_zero_of_forall_ne 1 (conductorCompletedL χ) hsum hsindex
  have hpd : P.derivative.eval s = P.coeff 1 := by
    have heq := congrArg Polynomial.derivative (Polynomial.eq_X_add_C_of_degree_le_one hP)
    simpa using congrArg (Polynomial.eval s) heq
  have hdexp : HasDerivAt (fun z : ℂ => Complex.exp (P.eval z))
      (Complex.exp (P.eval s) * P.derivative.eval s) s := by
    simpa only [Function.comp_def] using
      ((Complex.hasDerivAt_exp (P.eval s)).comp s (P.hasDerivAt s))
  have hexp : logDeriv (fun z : ℂ => Complex.exp (P.eval z)) s = P.coeff 1 := by
    rw [logDeriv_apply, hdexp.deriv,
      hpd]
    field_simp
  have hlog : logDeriv (conductorCompletedL χ) s = P.coeff 1 +
      ∑' p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ),
        (1 / (s - divisorZeroIndex₀Val p) + 1 / divisorZeroIndex₀Val p) := by
    calc
      _ = logDeriv (fun z => Complex.exp (P.eval z) *
          divisorCanonicalProduct 1 (conductorCompletedL χ) (Set.univ : Set ℂ) z) s :=
        congrArg (fun f : ℂ → ℂ => logDeriv f s) (funext hfac)
      _ = _ := by
        rw [logDeriv_mul (f := fun z : ℂ => Complex.exp (P.eval z)) s
          (Complex.exp_ne_zero (P.eval s)) hprod hdexp.differentiableAt
          (differentiableAt_divisorCanonicalProduct_univ 1 (conductorCompletedL χ) hsum s),
          hexp, logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne hsum hsindex]
  rw [hlog, add_sub_cancel_left]
  exact (summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq hsum hsindex).hasSum

end WeightedTorusJets

end
end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.WeightedTorusJets.conductorCompletedL_logDeriv_hasSum_jb247_oai := @OAI.Erdos970.WeightedTorusJets.conductorCompletedL_logDeriv_hasSum_jb247_oai
