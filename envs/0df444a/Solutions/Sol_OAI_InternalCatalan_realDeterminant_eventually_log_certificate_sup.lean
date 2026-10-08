-- Prove2me | solution 1 for OAI.InternalCatalan.realDeterminant_eventually_log_certificate_sup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:30:08.610769+00:00
-- url     : https://prove2.me/submissions/b97f4668-8bd7-456b-adf8-ffec8393cdf4

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_OAICatalanIrrationality

section
-- module Solutions.OAICatalan.Catalan.Estimates.BlaschkeComplex
namespace OAI

open scoped BigOperators

namespace InternalCatalan

noncomputable def blaschkeFactor (x : ℝ) (z : ℂ) : ℂ :=
  (z - (x : ℂ)) / (1 - (x : ℂ) * z)

noncomputable def finiteBlaschke {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, blaschkeFactor (x i) z

theorem blaschkeFactor_imaginary_norm_sq (u x : ℝ) :
    ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ ^ 2 =
      (u ^ 2 + x ^ 2) / (1 + x ^ 2 * u ^ 2) := by
  unfold blaschkeFactor
  rw [Complex.sq_norm, Complex.normSq_div]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one, sub_zero,
    zero_sub]
  congr 1 <;> ring

theorem blaschkeFactor_outer_one_le_norm {u x : ℝ}
    (hu : 1 ≤ u) (hx : x ^ 2 ≤ 1) :
    1 ≤ ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ := by
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have hden : 0 < 1 + x ^ 2 * u ^ 2 := by positivity
  have hnum : 1 + x ^ 2 * u ^ 2 ≤ u ^ 2 + x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu2) (sub_nonneg.mpr hx)]
  have hs : 1 ≤ ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ ^ 2 := by
    rw [blaschkeFactor_imaginary_norm_sq]
    exact (one_le_div hden).2 hnum
  nlinarith [norm_nonneg (blaschkeFactor x (Complex.I * (u : ℂ)))]


theorem finiteBlaschke_norm {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) :
    ‖finiteBlaschke s x z‖ = ∏ i ∈ s, ‖blaschkeFactor (x i) z‖ := by
  exact Complex.norm_prod s _

theorem finiteBlaschke_outer_one_le_norm {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) {u : ℝ} (hu : 1 ≤ u) (hx : ∀ i ∈ s, x i ^ 2 ≤ 1) :
    1 ≤ ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ := by
  rw [finiteBlaschke_norm]
  exact Finset.one_le_prod (fun i hi => blaschkeFactor_outer_one_le_norm hu (hx i hi))

theorem outer_diameter_power_le_exp_two {D n : ℕ} {u : ℝ}
    (hDn : D ≤ n) (hu : 1 ≤ u) (hun : u ≤ 1 + 2 / (n : ℝ)) :
    u ^ D ≤ Real.exp 2 := by
  calc
    u ^ D ≤ u ^ n := pow_le_pow_right₀ hu hDn
    _ ≤ (1 + 2 / (n : ℝ)) ^ n := pow_le_pow_left₀ (by linarith) hun n
    _ ≤ Real.exp 2 := by
      simpa only [neg_div, sub_neg_eq_add, neg_neg] using
        (Real.one_sub_div_pow_le_exp_neg (n := n) (t := -2)
          (le_trans (by norm_num) (Nat.cast_nonneg n)))

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.BlaschkeAnalytic
namespace OAI

noncomputable section
open scoped BigOperators
namespace InternalCatalan

theorem blaschkeFactor_denominator_ne_zero {x : ℝ} {z : ℂ}
    (hx : |x| < 1) (hz : ‖z‖ ≤ 1) : 1 - (x : ℂ) * z ≠ 0 := by
  have hm : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |x| * ‖z‖ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hz (abs_nonneg x)
      _ < 1 := by simpa only [mul_one] using hx
  intro h
  have heq : (x : ℂ) * z = 1 := (sub_eq_zero.mp h).symm
  rw [heq, norm_one] at hm
  exact (lt_irrefl 1) hm

theorem blaschkeFactor_imaginary_denominator_ne_zero (x u : ℝ) :
    1 - (x : ℂ) * (Complex.I * (u : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.mul_re, Complex.mul_im] at hre

theorem blaschkeFactor_imaginary_ne_zero_of_node_ne_zero {x : ℝ}
    (hx : x ≠ 0) (u : ℝ) : blaschkeFactor x (Complex.I * (u : ℂ)) ≠ 0 := by
  unfold blaschkeFactor
  apply div_ne_zero
  · intro h
    have hre : -x = 0 := by
      simpa [Complex.mul_re, Complex.mul_im] using congrArg Complex.re h
    exact hx (neg_eq_zero.mp hre)
  · exact blaschkeFactor_imaginary_denominator_ne_zero x u

theorem blaschkeFactor_analyticAt (x : ℝ) {z : ℂ}
    (hz : 1 - (x : ℂ) * z ≠ 0) : AnalyticAt ℂ (blaschkeFactor x) z := by
  change AnalyticAt ℂ (fun w : ℂ => (w - (x : ℂ)) / (1 - (x : ℂ) * w)) z
  have hid : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
  have hx : AnalyticAt ℂ (fun _ : ℂ => (x : ℂ)) z := analyticAt_const
  have h1 : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const
  exact (hid.sub hx).div (h1.sub (hx.mul hid)) hz

theorem finiteBlaschke_analyticAt {ι : Type*} (s : Finset ι) (x : ι → ℝ) {z : ℂ}
    (hz : ∀ i ∈ s, 1 - (x i : ℂ) * z ≠ 0) :
    AnalyticAt ℂ (finiteBlaschke s x) z := by
  classical
  revert hz
  induction s using Finset.induction_on with
  | empty =>
      intro _
      have hfun : finiteBlaschke (∅ : Finset ι) x = fun _ : ℂ => (1 : ℂ) := by
        funext w
        simp only [finiteBlaschke, Finset.prod_empty]
      rw [hfun]
      exact analyticAt_const
  | @insert i s hi ih =>
      intro hz
      have hhead := blaschkeFactor_analyticAt (x i) (hz i (Finset.mem_insert_self _ _))
      have htail := ih (fun j hj => hz j (Finset.mem_insert_of_mem hj))
      have hfun : finiteBlaschke (insert i s) x =
          fun w => blaschkeFactor (x i) w * finiteBlaschke s x w := by
        funext w
        simp only [finiteBlaschke, Finset.prod_insert hi]
      rw [hfun]
      exact hhead.mul htail


theorem finiteBlaschke_imaginary_ne_zero {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0) (u : ℝ) :
    finiteBlaschke s x (Complex.I * (u : ℂ)) ≠ 0 := by
  unfold finiteBlaschke
  exact Finset.prod_ne_zero_iff.mpr
    (fun i hi => blaschkeFactor_imaginary_ne_zero_of_node_ne_zero (hx i hi) u)

theorem finiteBlaschke_quotient_analyticAt_imaginary {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) (u : ℝ) :
    AnalyticAt ℂ (fun z : ℂ => z ^ D / finiteBlaschke s x z)
      (Complex.I * (u : ℂ)) := by
  have hp : AnalyticAt ℂ (fun z : ℂ => z ^ D) (Complex.I * (u : ℂ)) :=
    analyticAt_id.pow D
  exact hp.div
    (finiteBlaschke_analyticAt s x
      (fun i _ => blaschkeFactor_imaginary_denominator_ne_zero (x i) u))
    (finiteBlaschke_imaginary_ne_zero s x hx u)


theorem blaschkeFactor_norm_eq_one {x : ℝ} {z : ℂ}
    (hx : |x| < 1) (hz : ‖z‖ = 1) : ‖blaschkeFactor x z‖ = 1 := by
  have hzsq : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz]
    norm_num
  have hid : Complex.normSq (z - (x : ℂ)) - Complex.normSq (1 - (x : ℂ) * z) =
      (1 - x ^ 2) * (Complex.normSq z - 1) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, zero_mul, add_zero,
      sub_zero, zero_sub]
    ring
  rw [hzsq, sub_self, mul_zero] at hid
  have hsq := sub_eq_zero.mp hid
  have hnorm : ‖z - (x : ℂ)‖ = ‖1 - (x : ℂ) * z‖ := by
    simpa only [Complex.norm_def] using congrArg Real.sqrt hsq
  change ‖(z - (x : ℂ)) / (1 - (x : ℂ) * z)‖ = 1
  rw [norm_div, hnorm]
  exact div_self (norm_ne_zero_iff.mpr (blaschkeFactor_denominator_ne_zero hx hz.le))

theorem finiteBlaschke_norm_eq_one {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, |x i| < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖finiteBlaschke s x z‖ = 1 := by
  rw [finiteBlaschke_norm]
  apply Finset.prod_eq_one
  intro i hi
  exact blaschkeFactor_norm_eq_one (hx i hi) hz

theorem finiteBlaschke_eval_node {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {i : ι} (hi : i ∈ s) : finiteBlaschke s x (x i : ℂ) = 0 := by
  unfold finiteBlaschke
  apply Finset.prod_eq_zero hi
  simp only [blaschkeFactor, sub_self, zero_div]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.BlaschkeScalar
namespace OAI

noncomputable section
open Set

namespace InternalCatalan

def blaschkeWeight (x : ℝ) : ℝ := (1 - x ^ 2) / (1 + x ^ 2)

private def blaschkeLogDefect (a t : ℝ) : ℝ :=
  Real.log (t + a) - Real.log (1 + a * t) -
    (1 - a) / (1 + a) * Real.log t

private theorem blaschkeLogDefect_hasDerivAt {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) :
    HasDerivAt (blaschkeLogDefect a)
      (1 / (t + a) - a / (1 + a * t) - ((1 - a) / (1 + a)) / t) t := by
  have hn : t + a ≠ 0 := ne_of_gt (by positivity)
  have hd : 1 + a * t ≠ 0 := ne_of_gt (by positivity)
  have h := ((((hasDerivAt_id t).add_const a).log hn).sub
      ((((hasDerivAt_id t).const_mul a).const_add 1).log hd)).sub
      ((Real.hasDerivAt_log ht.ne').const_mul ((1 - a) / (1 + a)))
  simp only [id_eq, mul_one] at h
  change HasDerivAt (fun y : ℝ => Real.log (y + a) - Real.log (1 + a * y) -
      ((1 - a) / (1 + a)) * Real.log y)
    (1 / (t + a) - a / (1 + a * t) - ((1 - a) / (1 + a)) * t⁻¹) t at h
  change HasDerivAt (fun y : ℝ => Real.log (y + a) - Real.log (1 + a * y) -
      ((1 - a) / (1 + a)) * Real.log y) _ t
  simpa only [div_eq_mul_inv] using h

theorem blaschke_log_derivative_nonpos {a t : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 < t) :
    1 / (t + a) - a / (1 + a * t) - ((1 - a) / (1 + a)) / t ≤ 0 := by
  have hta : t + a ≠ 0 := ne_of_gt (by positivity)
  have hat : 1 + a * t ≠ 0 := ne_of_gt (by positivity)
  have ha' : 1 + a ≠ 0 := ne_of_gt (by positivity)
  have hid :
      1 / (t + a) - a / (1 + a * t) - ((1 - a) / (1 + a)) / t =
      -(a * (1 - a) * (t - 1) ^ 2) / ((t + a) * (1 + a * t) * (1 + a) * t) := by
    field_simp [hta, hat, ha', ht.ne']
    ring
  rw [hid]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1)) (sq_nonneg _))
  · positivity

theorem blaschke_log_ratio_lower {a t : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1) :
    (1 - a) / (1 + a) * Real.log t ≤
      Real.log (t + a) - Real.log (1 + a * t) := by
  have hanti : AntitoneOn (blaschkeLogDefect a) (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro y hy
      exact (blaschkeLogDefect_hasDerivAt ha hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (blaschkeLogDefect_hasDerivAt ha (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(blaschkeLogDefect_hasDerivAt ha (interior_subset hy)).deriv]
      exact blaschke_log_derivative_nonpos ha ha1 (interior_subset hy)
  have h := hanti ht (show (1 : ℝ) ∈ Ioi 0 by norm_num) ht1
  dsimp only [blaschkeLogDefect] at h
  simp only [mul_one, Real.log_one, mul_zero, add_comm 1 a, sub_self] at h
  rw [add_comm a 1] at h
  linarith

theorem blaschke_factor_log_lower {x u : ℝ}
    (hx : x ^ 2 ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1) :
    blaschkeWeight x * Real.log u ≤
      (Real.log (u ^ 2 + x ^ 2) - Real.log (1 + x ^ 2 * u ^ 2)) / 2 := by
  have h := blaschke_log_ratio_lower (sq_nonneg x) hx (sq_pos_of_pos hu)
    (show u ^ 2 ≤ 1 by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)])
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  dsimp only [blaschkeWeight]
  nlinarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.CauchyNumerics
namespace OAI

namespace InternalCatalan

theorem cauchy_radius_pos {n : ℕ} {r : ℝ} (hn : 48 ≤ n)
    (hr : 1 / (10 * (n : ℝ)) ≤ r) : 0 < r := by
  have hn48 : (48 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  exact lt_of_lt_of_le (by positivity) hr

theorem cauchy_numerical_bound {n : ℕ} {r E : ℝ}
    (hn : 48 ≤ n) (hr : 1 / (10 * (n : ℝ)) ≤ r) (hE : 0 ≤ E) :
    (3 / Real.pi) * (2 * (1 + 2 / (n : ℝ))) * E / r ≤
      30 * E * (n : ℝ) := by
  have hn48 : (48 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hrpos : 0 < r := cauchy_radius_pos hn hr
  have hpi : 3 / Real.pi ≤ 1 :=
    (div_le_iff₀ Real.pi_pos).mpr (by simpa only [one_mul] using Real.pi_gt_three.le)
  have hsmall : 2 / (n : ℝ) ≤ (1 : ℝ) / 2 :=
    (div_le_iff₀ hnpos).mpr (by linarith)
  have hlength : 2 * (1 + 2 / (n : ℝ)) ≤ 3 := by linarith
  have hcoefficient : (3 / Real.pi) * (2 * (1 + 2 / (n : ℝ))) ≤ 3 := by
    calc
      _ ≤ 1 * (2 * (1 + 2 / (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hpi (by positivity)
      _ ≤ 3 := by simpa only [one_mul] using hlength
  have hnr : 1 ≤ r * (10 * (n : ℝ)) :=
    (div_le_iff₀ (by positivity : 0 < 10 * (n : ℝ))).mp hr
  apply (div_le_iff₀ hrpos).mpr
  calc
    _ ≤ 3 * E := mul_le_mul_of_nonneg_right hcoefficient hE
    _ = (3 * E) * 1 := by ring
    _ ≤ (3 * E) * (r * (10 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hnr (mul_nonneg (by norm_num) hE)
    _ = (30 * E * (n : ℝ)) * r := by ring

theorem cauchy_exp_two_bound {n : ℕ} {r : ℝ}
    (hn : 48 ≤ n) (hr : 1 / (10 * (n : ℝ)) ≤ r) :
    (3 / Real.pi) * (2 * (1 + 2 / (n : ℝ))) * Real.exp 2 / r ≤
      30 * Real.exp 2 * (n : ℝ) :=
  cauchy_numerical_bound hn hr (Real.exp_pos 2).le

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.CauchyKernel
namespace OAI

noncomputable section

namespace InternalCatalan

section

open scoped BigOperators

theorem blaschkeFactor_imaginary_norm_pos (x : ℝ) {u : ℝ} (hu : 0 < u) :
    0 < ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ := by
  have hp : 0 < ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ ^ 2 := by
    rw [blaschkeFactor_imaginary_norm_sq]
    positivity
  nlinarith [norm_nonneg (blaschkeFactor x (Complex.I * (u : ℂ)))]

theorem blaschkeFactor_imaginary_lower {x u : ℝ}
    (hx : x ^ 2 ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1) :
    u ^ blaschkeWeight x ≤ ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ := by
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hu _)
    (blaschkeFactor_imaginary_norm_pos x hu), Real.log_rpow hu]
  have hlog := congrArg Real.log (blaschkeFactor_imaginary_norm_sq u x)
  rw [Real.log_pow, Real.log_div (by positivity) (by positivity)] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have h := blaschke_factor_log_lower hx hu hu1
  linarith

theorem finiteBlaschke_imaginary_lower {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {u : ℝ} (hx : ∀ i ∈ s, x i ^ 2 ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1) :
    u ^ (∑ i ∈ s, blaschkeWeight (x i)) ≤
      ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ := by
  rw [finiteBlaschke_norm, Real.rpow_sum_of_pos hu]
  exact Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hu _).le)
    (fun i hi => blaschkeFactor_imaginary_lower (hx i hi) hu hu1)

theorem finiteBlaschke_inner_quotient_le_one {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) {u : ℝ} (hx : ∀ i ∈ s, x i ^ 2 ≤ 1)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (hD : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ)) :
    ‖(Complex.I * (u : ℂ)) ^ D / finiteBlaschke s x (Complex.I * (u : ℂ))‖ ≤ 1 := by
  have hb := finiteBlaschke_imaginary_lower s x hx hu hu1
  have hp := Real.rpow_pos_of_pos hu (∑ i ∈ s, blaschkeWeight (x i))
  have hbp : 0 < ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ := lt_of_lt_of_le hp hb
  rw [norm_div, norm_pow, norm_mul, Complex.norm_I, Complex.norm_of_nonneg hu.le, one_mul]
  apply (div_le_one₀ hbp).mpr
  calc
    u ^ D = u ^ (D : ℝ) := (Real.rpow_natCast u D).symm
    _ ≤ u ^ (∑ i ∈ s, blaschkeWeight (x i)) :=
      Real.rpow_le_rpow_of_exponent_ge hu hu1 hD
    _ ≤ _ := hb

theorem finiteBlaschke_outer_quotient_le_exp_two {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) {u : ℝ} (hDn : D ≤ n)
    (hx : ∀ i ∈ s, x i ^ 2 ≤ 1) (hu : 1 ≤ u) (hun : u ≤ 1 + 2 / (n : ℝ)) :
    ‖(Complex.I * (u : ℂ)) ^ D / finiteBlaschke s x (Complex.I * (u : ℂ))‖ ≤
      Real.exp 2 := by
  have hb := finiteBlaschke_outer_one_le_norm s x hu hx
  have hbp : 0 < ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ := lt_of_lt_of_le zero_lt_one hb
  have hu0 : 0 ≤ u := by linarith
  rw [norm_div, norm_pow, norm_mul, Complex.norm_I, Complex.norm_of_nonneg hu0, one_mul]
  calc
    u ^ D / ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ ≤ u ^ D := by
      apply (div_le_iff₀ hbp).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (pow_nonneg hu0 D)
    _ ≤ Real.exp 2 := outer_diameter_power_le_exp_two hDn hu hun

theorem finiteBlaschke_imaginary_norm_abs {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (u : ℝ) :
    ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ =
      ‖finiteBlaschke s x (Complex.I * ((|u| : ℝ) : ℂ))‖ := by
  rw [finiteBlaschke_norm, finiteBlaschke_norm]
  apply Finset.prod_congr rfl
  intro i _
  have hsq : ‖blaschkeFactor (x i) (Complex.I * (u : ℂ))‖ ^ 2 =
      ‖blaschkeFactor (x i) (Complex.I * ((|u| : ℝ) : ℂ))‖ ^ 2 := by
    rw [blaschkeFactor_imaginary_norm_sq, blaschkeFactor_imaginary_norm_sq, sq_abs]
  nlinarith [norm_nonneg (blaschkeFactor (x i) (Complex.I * (u : ℂ))),
    norm_nonneg (blaschkeFactor (x i) (Complex.I * ((|u| : ℝ) : ℂ)))]

theorem finiteBlaschke_quotient_imaginary_norm_abs {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) (u : ℝ) :
    ‖(Complex.I * (u : ℂ)) ^ D / finiteBlaschke s x (Complex.I * (u : ℂ))‖ =
      ‖(Complex.I * ((|u| : ℝ) : ℂ)) ^ D /
        finiteBlaschke s x (Complex.I * ((|u| : ℝ) : ℂ))‖ := by
  simp only [norm_div, norm_pow, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, one_mul, abs_abs]
  rw [finiteBlaschke_imaginary_norm_abs s x u]

theorem finiteBlaschke_diameter_quotient_le_exp_two {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) {u : ℝ} (hDpos : 0 < D) (hDn : D ≤ n)
    (hx : ∀ i ∈ s, x i ^ 2 ≤ 1)
    (hD : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    (hu : |u| ≤ 1 + 2 / (n : ℝ)) :
    ‖(Complex.I * (u : ℂ)) ^ D / finiteBlaschke s x (Complex.I * (u : ℂ))‖ ≤
      Real.exp 2 := by
  rw [finiteBlaschke_quotient_imaginary_norm_abs s x D u]
  rcases eq_or_lt_of_le (abs_nonneg u) with hz | hp
  · rw [← hz]
    simpa only [Complex.ofReal_zero, mul_zero, zero_pow hDpos.ne', zero_div, norm_zero] using
      (Real.exp_pos 2).le
  · by_cases hi : |u| ≤ 1
    · exact (finiteBlaschke_inner_quotient_le_one s x D hx hp hi hD).trans
        (by simpa only [Real.exp_zero] using
          (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 by norm_num)))
    · exact finiteBlaschke_outer_quotient_le_exp_two s x D n hDn hx (le_of_not_ge hi) hu

end

section

open MeasureTheory Set
open scoped BigOperators Interval

def blaschkeDensity {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D : ℕ) (z : ℂ) : ℂ :=
  z ^ D / finiteBlaschke s x z

def blaschkeCauchyTransform {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ t in -(1 + 2 / (n : ℝ))..(1 + 2 / (n : ℝ)),
      (6 * blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)) * Complex.I

theorem imaginary_sub_ne_zero_of_re_ne_zero {z : ℂ} (hz : z.re ≠ 0) (t : ℝ) :
    Complex.I * (t : ℂ) - z ≠ 0 := by
  intro h
  have hre : -z.re = 0 := by
    simpa [Complex.mul_re, Complex.mul_im] using congrArg Complex.re h
  exact hz (neg_eq_zero.mp hre)

theorem abs_re_le_norm_imaginary_sub (z : ℂ) (t : ℝ) :
    |z.re| ≤ ‖Complex.I * (t : ℂ) - z‖ := by
  simpa [Complex.mul_re, Complex.mul_im] using
    Complex.abs_re_le_norm (Complex.I * (t : ℂ) - z)

theorem continuous_blaschkeDensity_imaginary {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) :
    Continuous (fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ))) := by
  have hpath : Continuous (fun t : ℝ => Complex.I * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  apply continuous_iff_continuousAt.mpr
  intro t
  change ContinuousAt
    (fun t : ℝ => (Complex.I * (t : ℂ)) ^ D /
      finiteBlaschke s x (Complex.I * (t : ℂ))) t
  have houter : ContinuousAt (fun w : ℂ => w ^ D / finiteBlaschke s x w)
      (Complex.I * (t : ℂ)) :=
    (finiteBlaschke_quotient_analyticAt_imaginary s x D hx t).continuousAt
  have hinner : ContinuousAt (fun u : ℝ => Complex.I * (u : ℂ)) t := hpath.continuousAt
  simpa only [Function.comp_def] using
    houter.comp (f := fun u : ℝ => Complex.I * (u : ℂ)) hinner

theorem continuous_blaschkeCauchyKernel {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ} (hz : z.re ≠ 0) :
    Continuous (fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)) := by
  exact (continuous_blaschkeDensity_imaginary s x D hx).div
    ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const)
    (imaginary_sub_ne_zero_of_re_ne_zero hz)


theorem blaschkeCauchyTransform_normalized {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (z : ℂ) :
    blaschkeCauchyTransform s x D n z = ((3 / Real.pi : ℝ) : ℂ) *
      ∫ t in -(1 + 2 / (n : ℝ))..(1 + 2 / (n : ℝ)),
        blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z) := by
  have hfun : (fun t : ℝ =>
      (6 * blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)) * Complex.I) =
      (fun t : ℝ => (6 * Complex.I) *
        (blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z))) := by
    funext t
    ring
  have hp : (Real.pi : ℂ) ≠ 0 := by
    intro h
    exact Real.pi_pos.ne' (by simpa using congrArg Complex.re h)
  have hcoeff : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (6 * Complex.I) =
      ((3 / Real.pi : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    field_simp [hp, Complex.I_ne_zero]
    ring
  unfold blaschkeCauchyTransform
  rw [hfun, intervalIntegral.integral_const_mul, ← mul_assoc, hcoeff]

theorem blaschkeCauchyTransform_norm_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hDpos : 0 < D) (hDn : D ≤ n)
    (hx : ∀ i ∈ s, x i ^ 2 ≤ 1)
    (hD : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : z.re ≠ 0) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤
      (3 / Real.pi) * (2 * (1 + 2 / (n : ℝ))) * Real.exp 2 / |z.re| := by
  let T : ℝ := 1 + 2 / (n : ℝ)
  have hT : 0 < T := by dsimp only [T]; positivity
  have hzr : 0 < |z.re| := abs_pos.mpr hz
  have hi : ‖∫ t in -T..T,
      blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖ ≤
      (Real.exp 2 / |z.re|) * (2 * T) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T) (b := T) (C := Real.exp 2 / |z.re|)
      (f := fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)) (fun t ht => by
          have ht' : t ∈ Ioc (-T) T := by
            simpa only [uIoc_of_le (show -T ≤ T by linarith)] using ht
          have htab : |t| ≤ 1 + 2 / (n : ℝ) := abs_le.mpr ⟨ht'.1.le, ht'.2⟩
          have hf : ‖blaschkeDensity s x D (Complex.I * (t : ℂ))‖ ≤ Real.exp 2 :=
            finiteBlaschke_diameter_quotient_le_exp_two s x D n hDpos hDn hx hD htab
          have hdist := abs_re_le_norm_imaginary_sub z t
          have hdistpos : 0 < ‖Complex.I * (t : ℂ) - z‖ := lt_of_lt_of_le hzr hdist
          rw [norm_div]
          exact (div_le_div_of_nonneg_right hf hdistpos.le).trans
            (div_le_div_of_nonneg_left (Real.exp_pos 2).le hzr hdist))
    have hlen : |T - -T| = 2 * T := by rw [abs_of_pos (by linarith)]; ring
    simpa only [hlen] using hbound
  rw [blaschkeCauchyTransform_normalized, norm_mul,
    Complex.norm_of_nonneg (show 0 ≤ 3 / Real.pi by positivity)]
  calc
    (3 / Real.pi) * ‖∫ t in -(1 + 2 / (n : ℝ))..(1 + 2 / (n : ℝ)),
        blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖
      ≤ (3 / Real.pi) * ((Real.exp 2 / |z.re|) * (2 * T)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (3 / Real.pi) * (2 * (1 + 2 / (n : ℝ))) * Real.exp 2 / |z.re| := by
      dsimp only [T]
      ring

theorem blaschkeCauchyTransform_far_axis_bound {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n) (hDpos : 0 < D) (hDn : D ≤ n)
    (hx : ∀ i ∈ s, x i ^ 2 ≤ 1)
    (hD : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : 1 / (10 * (n : ℝ)) ≤ |z.re|) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤ 30 * Real.exp 2 * (n : ℝ) := by
  have hz0 : z.re ≠ 0 := abs_pos.mp (cauchy_radius_pos hn hz)
  exact (blaschkeCauchyTransform_norm_le s x D n hDpos hDn hx hD hz0).trans
    (cauchy_exp_two_bound hn hz)

end

section

open MeasureTheory Set Metric
open scoped Topology Interval









end

open scoped BigOperators



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.BlaschkeDensityPolynomial
namespace OAI

noncomputable section
open Polynomial
open scoped BigOperators
namespace InternalCatalan

def blaschkeNodePolynomial {ι : Type*} (s : Finset ι) (x : ι → ℝ) : ℂ[X] :=
  ∏ i ∈ s, (X - C (x i : ℂ))

def blaschkeDensityNumerator {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D : ℕ) : ℂ[X] :=
  X ^ D * ∏ i ∈ s, (1 - C (x i : ℂ) * X)

theorem blaschkeDensity_eq_product {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (z : ℂ) :
    blaschkeDensity s x D z = z ^ D * ∏ i ∈ s, (1 - (x i : ℂ) * z) / (z - (x i : ℂ)) := by
  unfold blaschkeDensity finiteBlaschke blaschkeFactor
  rw [div_eq_mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [inv_div]

theorem blaschkeDensity_eq_eval_div {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (z : ℂ) :
    blaschkeDensity s x D z =
      (blaschkeDensityNumerator s x D).eval z / (blaschkeNodePolynomial s x).eval z := by
  simp only [blaschkeDensityNumerator, blaschkeNodePolynomial, eval_mul, eval_pow,
    eval_X, eval_prod, eval_sub, eval_one, eval_C]
  rw [blaschkeDensity_eq_product, Finset.prod_div_distrib]
  ring

theorem blaschkeNodePolynomial_eval_ne_zero_iff {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (z : ℂ) :
    (blaschkeNodePolynomial s x).eval z ≠ 0 ↔ ∀ i ∈ s, z ≠ (x i : ℂ) := by
  simp only [blaschkeNodePolynomial, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_ne_zero_iff, sub_ne_zero]

theorem blaschkeNodePolynomial_eval_imaginary_ne_zero {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0) (u : ℝ) :
    (blaschkeNodePolynomial s x).eval (Complex.I * (u : ℂ)) ≠ 0 := by
  apply (blaschkeNodePolynomial_eval_ne_zero_iff s x _).mpr
  intro i hi h
  have hre : (0 : ℝ) = x i := by
    simpa [Complex.mul_re, Complex.mul_im] using congrArg Complex.re h
  exact hx i hi hre.symm

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.BlaschkeEndpointGeometry
namespace OAI

noncomputable section

namespace InternalCatalan

section

open scoped BigOperators

theorem reciprocal_blaschkeFactor_endpoint_norm_le {x : ℝ} (hx : |x| < 1)
    {c w : ℂ} (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
    ‖(1 - (x : ℂ) * w) / (w - (x : ℂ))‖ ≤ 1 + 3 * ‖w - c‖ := by
  let d := ‖w - c‖
  let a := ‖c - (x : ℂ)‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have ha : 1 ≤ a := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, hci] using
      Complex.abs_im_le_norm (c - (x : ℂ))
  have hcenter : ‖1 - (x : ℂ) * c‖ = a := by
    have hr := blaschkeFactor_norm_eq_one hx hc
    unfold blaschkeFactor at hr
    rw [norm_div] at hr
    have heq := (div_eq_iff (norm_ne_zero_iff.mpr
      (blaschkeFactor_denominator_ne_zero hx hc.le))).mp hr
    simpa only [one_mul] using heq.symm
  have hdenlower : a - d ≤ ‖w - (x : ℂ)‖ := by
    have ht := norm_sub_norm_le (c - (x : ℂ)) (w - (x : ℂ))
    have heq : (c - (x : ℂ)) - (w - (x : ℂ)) = c - w := by ring
    rw [heq, norm_sub_rev c w] at ht
    change a - ‖w - (x : ℂ)‖ ≤ d at ht
    linarith
  have hdenpos : 0 < ‖w - (x : ℂ)‖ := by
    change d ≤ 1 / 4 at hd
    linarith
  have hnum : ‖1 - (x : ℂ) * w‖ ≤ a + d := by
    have heq : 1 - (x : ℂ) * w = (1 - (x : ℂ) * c) - (x : ℂ) * (w - c) := by ring
    rw [heq]
    calc
      _ ≤ ‖1 - (x : ℂ) * c‖ + ‖(x : ℂ) * (w - c)‖ := norm_sub_le _ _
      _ = a + |x| * d := by rw [hcenter, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ a + d := by nlinarith [mul_le_mul_of_nonneg_right hx.le hd0]
  rw [norm_div]
  apply (div_le_iff₀ hdenpos).mpr
  calc
    _ ≤ a + d := hnum
    _ ≤ (1 + 3 * d) * (a - d) := by
      have hprod := mul_nonneg hd0 (sub_nonneg.mpr ha)
      have hquad := mul_nonneg hd0 (sub_nonneg.mpr hd)
      nlinarith
    _ ≤ (1 + 3 * d) * ‖w - (x : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hdenlower (by positivity)

theorem blaschkeDensity_endpoint_norm_le_exp {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (hx : ∀ i ∈ s, |x i| < 1) {c w : ℂ}
    (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
    ‖blaschkeDensity s x D w‖ ≤
      Real.exp (((D : ℝ) + 3 * (s.card : ℝ)) * ‖w - c‖) := by
  let d := ‖w - c‖
  have hwp : ‖w‖ ≤ Real.exp d := by
    calc
      ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by simpa using norm_add_le (w - c) c
      _ = d + 1 := by rw [hc]
      _ ≤ Real.exp d := Real.add_one_le_exp d
  have hpow : ‖w‖ ^ D ≤ (Real.exp d) ^ D :=
    pow_le_pow_left₀ (norm_nonneg _) hwp _
  have hf (i : ι) (hi : i ∈ s) :
      ‖(1 - (x i : ℂ) * w) / (w - (x i : ℂ))‖ ≤ Real.exp (3 * d) :=
    (reciprocal_blaschkeFactor_endpoint_norm_le (hx i hi) hc hci hd).trans
      (by simpa only [add_comm] using Real.add_one_le_exp (3 * d))
  have hp := Finset.prod_le_prod (fun i (_ : i ∈ s) =>
    norm_nonneg ((1 - (x i : ℂ) * w) / (w - (x i : ℂ)))) hf
  rw [blaschkeDensity_eq_product, norm_mul, norm_pow, norm_prod]
  calc
    _ ≤ (Real.exp d) ^ D * ∏ _i ∈ s, Real.exp (3 * d) :=
      mul_le_mul hpow hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = Real.exp (((D : ℝ) + 3 * (s.card : ℝ)) * d) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem blaschkeDensity_endpoint_norm_le_exp_twelve {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx : ∀ i ∈ s, |x i| < 1)
    {c w : ℂ} (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ 3 / (n : ℝ)) :
    ‖blaschkeDensity s x D w‖ ≤ Real.exp 12 := by
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hquarter : ‖w - c‖ ≤ (1 / 4 : ℝ) := hd.trans ((div_le_iff₀ hnpos).mpr (by linarith))
  apply (blaschkeDensity_endpoint_norm_le_exp s x D hx hc hci hquarter).trans
  apply Real.exp_le_exp.mpr
  have hDn : (D : ℝ) ≤ n := by exact_mod_cast hD
  have hcn : (s.card : ℝ) ≤ n := by exact_mod_cast hcard
  have hmul := (le_div_iff₀ hnpos).mp hd
  have h1 := mul_le_mul_of_nonneg_right hDn (norm_nonneg (w - c))
  have h2 := mul_le_mul_of_nonneg_right hcn (norm_nonneg (w - c))
  nlinarith


end

theorem norm_ge_three_quarters_near_unit {c w : ℂ} (hc : ‖c‖ = 1)
    (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) : (3 / 4 : ℝ) ≤ ‖w‖ := by
  have ht := norm_sub_norm_le c w
  rw [hc, norm_sub_rev] at ht
  linarith

theorem blaschkeFactor_endpoint_norm_lower {x : ℝ} (hx : |x| < 1) {c w : ℂ}
    (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
    (3 / 4 : ℝ) ≤ ‖w - (x : ℂ)‖ ∧ (3 / 4 : ℝ) ≤ ‖1 - (x : ℂ) * w‖ := by
  have ha : 1 ≤ ‖c - (x : ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, hci] using
      Complex.abs_im_le_norm (c - (x : ℂ))
  have hcenter : ‖1 - (x : ℂ) * c‖ = ‖c - (x : ℂ)‖ := by
    have hr := blaschkeFactor_norm_eq_one hx hc
    unfold blaschkeFactor at hr
    rw [norm_div] at hr
    have heq := (div_eq_iff (norm_ne_zero_iff.mpr
      (blaschkeFactor_denominator_ne_zero hx hc.le))).mp hr
    simpa only [one_mul] using heq.symm
  constructor
  · have ht := norm_sub_norm_le (c - (x : ℂ)) (w - (x : ℂ))
    have heq : (c - (x : ℂ)) - (w - (x : ℂ)) = c - w := by ring
    rw [heq, norm_sub_rev c w] at ht
    linarith
  · have ht := norm_sub_norm_le (1 - (x : ℂ) * c) (1 - (x : ℂ) * w)
    have heq : (1 - (x : ℂ) * c) - (1 - (x : ℂ) * w) = (x : ℂ) * (w - c) := by ring
    rw [heq, hcenter, norm_mul, Complex.norm_real, Real.norm_eq_abs] at ht
    have hmul := mul_le_mul_of_nonneg_right hx.le (norm_nonneg (w - c))
    linarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.BlaschkeDensityLogDerivative
namespace OAI

noncomputable section
open scoped BigOperators
namespace InternalCatalan

private theorem reciprocalFactor_hasDerivAt (x : ℝ) {w : ℂ} (hw : w - (x : ℂ) ≠ 0) :
    HasDerivAt (fun v : ℂ => (1 - (x : ℂ) * v) / (v - (x : ℂ)))
      (((x : ℂ) ^ 2 - 1) / (w - (x : ℂ)) ^ 2) w := by
  have hn : HasDerivAt (fun v : ℂ => 1 - (x : ℂ) * v) (-(x : ℂ)) w := by
    convert! HasDerivAt.const_sub 1 ((hasDerivAt_id w).const_mul (x : ℂ)) using 1
    simp only [mul_one]
  have hd : HasDerivAt (fun v : ℂ => v - (x : ℂ)) 1 w := (hasDerivAt_id w).sub_const _
  convert! hn.div hd hw using 1
  ring

private theorem reciprocalFactor_logDeriv (x : ℝ) {w : ℂ}
    (hn : 1 - (x : ℂ) * w ≠ 0) (hd : w - (x : ℂ) ≠ 0) :
    logDeriv (fun v : ℂ => (1 - (x : ℂ) * v) / (v - (x : ℂ))) w =
      -(x : ℂ) / (1 - (x : ℂ) * w) - 1 / (w - (x : ℂ)) := by
  rw [logDeriv_apply, (reciprocalFactor_hasDerivAt x hd).deriv]
  field_simp [hn, hd]
  ring

theorem blaschkeDensity_logDeriv {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D : ℕ)
    {w : ℂ} (hw : w ≠ 0)
    (hnum : ∀ i ∈ s, 1 - (x i : ℂ) * w ≠ 0)
    (hden : ∀ i ∈ s, w - (x i : ℂ) ≠ 0) :
    logDeriv (blaschkeDensity s x D) w = (D : ℂ) / w +
      ∑ i ∈ s, (-(x i : ℂ) / (1 - (x i : ℂ) * w) - 1 / (w - (x i : ℂ))) := by
  classical
  let f : ι → ℂ → ℂ := fun i v => (1 - (x i : ℂ) * v) / (v - (x i : ℂ))
  have hfn : ∀ i ∈ s, f i w ≠ 0 := fun i hi => div_ne_zero (hnum i hi) (hden i hi)
  have hfd : ∀ i ∈ s, DifferentiableAt ℂ (f i) w :=
    fun i hi => (reciprocalFactor_hasDerivAt (x i) (hden i hi)).differentiableAt
  have hpn : (∏ i ∈ s, f i w) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfn
  have hpd : DifferentiableAt ℂ (fun v => ∏ i ∈ s, f i v) w :=
    DifferentiableAt.fun_finsetProd hfd
  have hfun : blaschkeDensity s x D = fun v => v ^ D * ∏ i ∈ s, f i v :=
    funext (blaschkeDensity_eq_product s x D)
  have hmul : logDeriv (fun v : ℂ => v ^ D * ∏ i ∈ s, f i v) w =
      logDeriv (fun v : ℂ => v ^ D) w + logDeriv (fun v : ℂ => ∏ i ∈ s, f i v) w := by
    convert! logDeriv_mul (f := fun v : ℂ => v ^ D)
      (g := fun v : ℂ => ∏ i ∈ s, f i v) w (pow_ne_zero D hw) hpn
      (differentiableAt_id.pow D) hpd using 1
  have hpow : logDeriv (fun v : ℂ => v ^ D) w = (D : ℂ) / w := by
    convert! logDeriv_pow w D using 1
  have hprod : logDeriv (fun v : ℂ => ∏ i ∈ s, f i v) w =
      ∑ i ∈ s, logDeriv (f i) w := by
    convert! logDeriv_prod hfn hfd using 1
  rw [hfun, hmul, hpow, hprod]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact reciprocalFactor_logDeriv (x i) (hnum i hi) (hden i hi)

theorem blaschkeDensity_endpoint_ne_zero {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (hx : ∀ i ∈ s, |x i| < 1) {c w : ℂ}
    (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
    blaschkeDensity s x D w ≠ 0 := by
  have hw : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num)
    (norm_ge_three_quarters_near_unit hc hd))
  rw [blaschkeDensity_eq_product]
  apply mul_ne_zero (pow_ne_zero D hw)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hh := blaschkeFactor_endpoint_norm_lower (hx i hi) hc hci hd
  exact div_ne_zero (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hh.2))
    (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hh.1))

theorem blaschkeDensity_endpoint_logDeriv_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx : ∀ i ∈ s, |x i| < 1) {c w : ℂ}
    (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
    ‖logDeriv (blaschkeDensity s x D) w‖ ≤ 4 * (n : ℝ) := by
  have hlow := norm_ge_three_quarters_near_unit hc hd
  have hwp : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hlow
  have hw : w ≠ 0 := norm_pos_iff.mp hwp
  have hlowi (i : ι) (hi : i ∈ s) := blaschkeFactor_endpoint_norm_lower (hx i hi) hc hci hd
  have hnum : ∀ i ∈ s, 1 - (x i : ℂ) * w ≠ 0 := fun i hi =>
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hlowi i hi).2)
  have hden : ∀ i ∈ s, w - (x i : ℂ) ≠ 0 := fun i hi =>
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hlowi i hi).1)
  have hp : ‖(D : ℂ) / w‖ ≤ (4 / 3 : ℝ) * (D : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hwp).mpr
    have hm := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg D)
    nlinarith
  have hf (i : ι) (hi : i ∈ s) :
      ‖-(x i : ℂ) / (1 - (x i : ℂ) * w) - 1 / (w - (x i : ℂ))‖ ≤ (8 / 3 : ℝ) := by
    have hnpos : 0 < ‖1 - (x i : ℂ) * w‖ := norm_pos_iff.mpr (hnum i hi)
    have hdpos : 0 < ‖w - (x i : ℂ)‖ := norm_pos_iff.mpr (hden i hi)
    have hn1 : |x i| / ‖1 - (x i : ℂ) * w‖ ≤ (4 / 3 : ℝ) := by
      apply (div_le_iff₀ hnpos).mpr
      nlinarith [(hlowi i hi).2, hx i hi]
    have hd1 : (1 : ℝ) / ‖w - (x i : ℂ)‖ ≤ (4 / 3 : ℝ) := by
      apply (div_le_iff₀ hdpos).mpr
      nlinarith [(hlowi i hi).1]
    calc
      _ ≤ ‖-(x i : ℂ) / (1 - (x i : ℂ) * w)‖ + ‖1 / (w - (x i : ℂ))‖ := norm_sub_le _ _
      _ ≤ (8 / 3 : ℝ) := by
        rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_one]
        linarith
  rw [blaschkeDensity_logDeriv s x D hw hnum hden]
  calc
    _ ≤ ‖(D : ℂ) / w‖ + ‖∑ i ∈ s,
        (-(x i : ℂ) / (1 - (x i : ℂ) * w) - 1 / (w - (x i : ℂ)))‖ := norm_add_le _ _
    _ ≤ (4 / 3 : ℝ) * (D : ℝ) + ∑ _i ∈ s, (8 / 3 : ℝ) :=
      add_le_add hp ((norm_sum_le _ _).trans (Finset.sum_le_sum hf))
    _ ≤ 4 * (n : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hDn : (D : ℝ) ≤ n := by exact_mod_cast hD
      have hcn : (s.card : ℝ) ≤ n := by exact_mod_cast hcard
      linarith

theorem blaschkeDensity_endpoint_deriv_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx : ∀ i ∈ s, |x i| < 1)
    {c w : ℂ} (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ 3 / (n : ℝ)) :
    ‖deriv (blaschkeDensity s x D) w‖ ≤ 4 * (n : ℝ) * Real.exp 12 := by
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hquarter : ‖w - c‖ ≤ (1 / 4 : ℝ) := hd.trans ((div_le_iff₀ hnpos).mpr (by linarith))
  have hF := blaschkeDensity_endpoint_ne_zero s x D hx hc hci hquarter
  have heq : deriv (blaschkeDensity s x D) w =
      logDeriv (blaschkeDensity s x D) w * blaschkeDensity s x D w := by
    rw [logDeriv_apply, div_mul_cancel₀ _ hF]
  rw [heq, norm_mul]
  exact mul_le_mul (blaschkeDensity_endpoint_logDeriv_norm_le s x D n hD hcard hx hc hci hquarter)
    (blaschkeDensity_endpoint_norm_le_exp_twelve s x D n hn hD hcard hx hc hci hd)
    (norm_nonneg _) (by positivity)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.CauchyLogJump
namespace OAI

noncomputable section
namespace InternalCatalan

theorem complex_log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.log (-w) = Complex.log w - (Real.pi : ℂ) * Complex.I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw,
    Complex.ofReal_sub]
  ring

theorem complex_log_neg_of_im_neg {w : ℂ} (hw : w.im < 0) :
    Complex.log (-w) = Complex.log w + (Real.pi : ℂ) * Complex.I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw,
    Complex.ofReal_add]
  ring

def cauchyLogLeft (T : ℝ) (z : ℂ) : ℂ :=
  -Complex.I * (Complex.log (Complex.I * (T : ℂ) - z) -
    Complex.log (-Complex.I * (T : ℂ) - z))

def cauchyLogRight (T : ℝ) (z : ℂ) : ℂ :=
  -Complex.I * (Complex.log (z - Complex.I * (T : ℂ)) -
    Complex.log (z + Complex.I * (T : ℂ)))

theorem cauchyLogLeft_sub_cauchyLogRight {T : ℝ} {z : ℂ}
    (hlo : -T < z.im) (hhi : z.im < T) :
    cauchyLogLeft T z - cauchyLogRight T z = 2 * (Real.pi : ℂ) := by
  have ha : 0 < (Complex.I * (T : ℂ) - z).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    linarith
  have hb : (-Complex.I * (T : ℂ) - z).im < 0 := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, neg_mul, one_mul, zero_add]
    linarith
  have hnegA : z - Complex.I * (T : ℂ) = -(Complex.I * (T : ℂ) - z) := by ring
  have hnegB : z + Complex.I * (T : ℂ) = -(-Complex.I * (T : ℂ) - z) := by ring
  unfold cauchyLogLeft cauchyLogRight
  rw [hnegA, hnegB, complex_log_neg_of_im_pos ha, complex_log_neg_of_im_neg hb]
  calc
    _ = -(2 * (Real.pi : ℂ)) * (Complex.I * Complex.I) := by ring
    _ = 2 * (Real.pi : ℂ) := by rw [Complex.I_mul_I]; ring


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.CauchyLocalLogBound
namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set
open scoped Interval

private theorem imaginary_path_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.I * (u : ℂ)) Complex.I t := by
  have hof : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
  convert! hof.const_mul Complex.I using 1
  simp

theorem cauchyLogLeftPrimitive_hasDerivAt {z : ℂ} (hz : z.re < 0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => -Complex.I * Complex.log (Complex.I * (u : ℂ) - z))
      (1 / (Complex.I * (t : ℂ) - z)) t := by
  have hd : HasDerivAt (fun u : ℝ => Complex.I * (u : ℂ) - z) Complex.I t :=
    (imaginary_path_hasDerivAt t).sub_const z
  have hslit : Complex.I * (t : ℂ) - z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa [Complex.mul_re, Complex.mul_im] using neg_pos.mpr hz
  have hh := (hd.clog_real hslit).const_mul (-Complex.I)
  convert! hh using 1
  simp only [← mul_div_assoc, neg_mul, Complex.I_mul_I, neg_neg]

theorem cauchyLogRightPrimitive_hasDerivAt {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    HasDerivAt (fun u : ℝ => -Complex.I * Complex.log (z - Complex.I * (u : ℂ)))
      (1 / (Complex.I * (t : ℂ) - z)) t := by
  have hd : HasDerivAt (fun u : ℝ => z - Complex.I * (u : ℂ)) (-Complex.I) t :=
    HasDerivAt.const_sub z (imaginary_path_hasDerivAt t)
  have hslit : z - Complex.I * (t : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa [Complex.mul_re, Complex.mul_im] using hz
  have hh := (hd.clog_real hslit).const_mul (-Complex.I)
  convert! hh using 1
  rw [show z - Complex.I * (t : ℂ) = -(Complex.I * (t : ℂ) - z) by ring]
  simp only [div_neg, neg_div, neg_neg, ← mul_div_assoc, neg_mul, Complex.I_mul_I]

theorem intervalIntegrable_cauchyConstantKernel (T : ℝ) {z : ℂ} (hz : z.re ≠ 0) :
    IntervalIntegrable (fun t : ℝ => (1 : ℂ) / (Complex.I * (t : ℂ) - z)) volume (-T) T := by
  have hc : Continuous (fun t : ℝ => (1 : ℂ) / (Complex.I * (t : ℂ) - z)) :=
    continuous_const.div
      ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const)
      (imaginary_sub_ne_zero_of_re_ne_zero hz)
  exact hc.intervalIntegrable _ _

theorem integral_cauchyConstantKernel_eq_left (T : ℝ) {z : ℂ} (hz : z.re < 0) :
    (∫ t in -T..T, (1 : ℂ) / (Complex.I * (t : ℂ) - z)) = cauchyLogLeft T z := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (-T) T) => cauchyLogLeftPrimitive_hasDerivAt hz t)
    (intervalIntegrable_cauchyConstantKernel T hz.ne)
  rw [hi]
  unfold cauchyLogLeft
  simp only [Complex.ofReal_neg, mul_neg, neg_mul]
  ring

theorem integral_cauchyConstantKernel_eq_right (T : ℝ) {z : ℂ} (hz : 0 < z.re) :
    (∫ t in -T..T, (1 : ℂ) / (Complex.I * (t : ℂ) - z)) = cauchyLogRight T z := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (-T) T) => cauchyLogRightPrimitive_hasDerivAt hz t)
    (intervalIntegrable_cauchyConstantKernel T hz.ne')
  rw [hi]
  unfold cauchyLogRight
  simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add]
  ring

open MeasureTheory Set
open scoped Interval

theorem log_two_mul_nat_le (n : ℕ) (hn : 0 < n) :
    Real.log (2 * (n : ℝ)) ≤ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.log_mul (by norm_num) hnR.ne']
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hnlog := Real.log_le_sub_one_of_pos hnR
  linarith

theorem complex_log_norm_le_nat_add_pi (n : ℕ) (hn : 0 < n) {w : ℂ}
    (hlo : 1 / (2 * (n : ℝ)) ≤ ‖w‖) (hhi : ‖w‖ ≤ 1) :
    ‖Complex.log w‖ ≤ (n : ℝ) + Real.pi := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hloglo : -Real.log (2 * (n : ℝ)) ≤ Real.log ‖w‖ := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < 1 / (2 * (n : ℝ))) hlo
    simpa only [one_div, Real.log_inv] using hh
  have hloghi : Real.log ‖w‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hhi
  have habs : |Real.log ‖w‖| ≤ (n : ℝ) := by
    rw [abs_of_nonpos hloghi]
    linarith [log_two_mul_nat_le n hn]
  calc
    _ ≤ |(Complex.log w).re| + |(Complex.log w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (n : ℝ) + Real.pi := by
      rw [Complex.log_re, Complex.log_im]
      exact add_le_add habs (Complex.abs_arg_le_pi w)

theorem intervalIntegrable_cauchyConstantKernel_interval (a b : ℝ) {z : ℂ} (hz : z.re ≠ 0) :
    IntervalIntegrable (fun t : ℝ => (1 : ℂ) / (Complex.I * (t : ℂ) - z)) volume a b := by
  have hc : Continuous (fun t : ℝ => (1 : ℂ) / (Complex.I * (t : ℂ) - z)) :=
    continuous_const.div
      ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const)
      (imaginary_sub_ne_zero_of_re_ne_zero hz)
  exact hc.intervalIntegrable _ _

theorem cauchyConstantKernel_interval_norm_le_three_mul (n : ℕ) (hn : 48 ≤ n)
    (a b : ℝ) {z : ℂ} (hz : z.re ≠ 0)
    (hal : 1 / (2 * (n : ℝ)) ≤ ‖Complex.I * (a : ℂ) - z‖)
    (hau : ‖Complex.I * (a : ℂ) - z‖ ≤ 1)
    (hbl : 1 / (2 * (n : ℝ)) ≤ ‖Complex.I * (b : ℂ) - z‖)
    (hbu : ‖Complex.I * (b : ℂ) - z‖ ≤ 1) :
    ‖∫ t in a..b, (1 : ℂ) / (Complex.I * (t : ℂ) - z)‖ ≤ 3 * (n : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hfinal : 2 * ((n : ℝ) + Real.pi) ≤ 3 * (n : ℝ) := by linarith [Real.pi_lt_four]
  rcases lt_or_gt_of_ne hz with hz | hz
  · have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t (_ : t ∈ uIcc a b) => cauchyLogLeftPrimitive_hasDerivAt hz t)
      (intervalIntegrable_cauchyConstantKernel_interval a b hz.ne)
    rw [hi]
    calc
      _ ≤ ‖-Complex.I * Complex.log (Complex.I * (b : ℂ) - z)‖ +
          ‖-Complex.I * Complex.log (Complex.I * (a : ℂ) - z)‖ := norm_sub_le _ _
      _ ≤ 2 * ((n : ℝ) + Real.pi) := by
        simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
        linarith [complex_log_norm_le_nat_add_pi n hn0 hal hau,
          complex_log_norm_le_nat_add_pi n hn0 hbl hbu]
      _ ≤ 3 * (n : ℝ) := hfinal
  · have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t (_ : t ∈ uIcc a b) => cauchyLogRightPrimitive_hasDerivAt hz t)
      (intervalIntegrable_cauchyConstantKernel_interval a b hz.ne')
    have ha1 : 1 / (2 * (n : ℝ)) ≤ ‖z - Complex.I * (a : ℂ)‖ := by rwa [norm_sub_rev]
    have ha2 : ‖z - Complex.I * (a : ℂ)‖ ≤ 1 := by rwa [norm_sub_rev]
    have hb1 : 1 / (2 * (n : ℝ)) ≤ ‖z - Complex.I * (b : ℂ)‖ := by rwa [norm_sub_rev]
    have hb2 : ‖z - Complex.I * (b : ℂ)‖ ≤ 1 := by rwa [norm_sub_rev]
    rw [hi]
    calc
      _ ≤ ‖-Complex.I * Complex.log (z - Complex.I * (b : ℂ))‖ +
          ‖-Complex.I * Complex.log (z - Complex.I * (a : ℂ))‖ := norm_sub_le _ _
      _ ≤ 2 * ((n : ℝ) + Real.pi) := by
        simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
        linarith [complex_log_norm_le_nat_add_pi n hn0 ha1 ha2,
          complex_log_norm_le_nat_add_pi n hn0 hb1 hb2]
      _ ≤ 3 * (n : ℝ) := hfinal

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.TwoAdicQuadratic
namespace OAI

namespace InternalCatalan

section

def L (N : ℕ) : ℕ := 59 * N
def A (N : ℕ) : ℕ := 19 * N





theorem H_eq_Cdegree_add_h (N : ℕ) : H N = Cdegree N + h N := by
  unfold H Cdegree h
  omega


theorem Cdegree_pos {N : ℕ} (hN : 0 < N) : 0 < Cdegree N := by
  unfold Cdegree
  omega



theorem rowDistance_le {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    rowDistance N r ≤ n N - 1 - g N := by
  unfold rowDistance rowOffset n g at *
  omega

theorem rowDistance_lt_Cdegree {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    rowDistance N r < Cdegree N := by
  have hd := rowDistance_le hN hr
  unfold n g Cdegree at *
  omega






theorem energy_abs_node_exponent {N : ℕ} (hN : 0 < N) :
    ((Cdegree N - 1 : ℕ) : ℤ) + (g N : ℤ) - ((n N - 1 : ℕ) : ℤ) =
      (A N : ℤ) := by
  unfold Cdegree g n A
  omega

theorem energy_parameter_ratios {N : ℕ} (hN : 0 < N) :
    (A N : ℝ) / (n N : ℝ) = 19 / 48 ∧
    ((2 * h N : ℕ) : ℝ) / (n N : ℝ) = 1 / 12 ∧
    (b N : ℝ) / (n N : ℝ) = 7 / 48 ∧
    (q N : ℝ) / (n N : ℝ) = 1 / 12 ∧
    (Cdegree N : ℝ) / (n N : ℝ) = 21 / 16 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [A, h, b, q, Cdegree, n, Nat.cast_mul, Nat.cast_ofNat] <;>
    field_simp [hN0] <;> ring



theorem energy_constant_after_squares {N : ℕ} (hN : 0 < N) (k : ℝ) :
    ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 -
        (k + 1) / (2 * (n N : ℝ))) - k / 2 - 1 =
      (-1 + 11 / 48 + 4 / 48 : ℝ) - (k + 1) / (2 * (n N : ℝ)) := by
  rw [(energy_parameter_ratios hN).2.2.2.2]
  ring

end

noncomputable section
open Set
open scoped BigOperators

theorem energy_log_one_add_sq_bounds {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ Real.log (1 + x ^ 2) ∧ Real.log (1 + x ^ 2) ≤ Real.log 2 := by
  have hp : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1])
  constructor
  · exact Real.log_nonneg (by nlinarith [sq_nonneg x])
  · exact Real.log_le_log (by positivity) (by nlinarith)

theorem realEnergyFiniteCorrection_bounds {N : ℕ} (hN : 0 < N)
    (k : ℝ) (hk : k = 1 ∨ k = 2) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    (0 ≤ (1 / (n N : ℝ)) *
      ∑ i : Fin (n N), ((k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2))) ∧
    ((1 / (n N : ℝ)) *
      ∑ i : Fin (n N), ((k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2))) ≤
      2 * Real.log 2 / (n N : ℝ) := by
  have hn : 0 < (n N : ℝ) :=
    Nat.cast_pos.mpr (show 0 < n N by unfold n; omega)
  have hk0 : 0 ≤ k + 2 := by
    rcases hk with rfl | rfl <;> norm_num
  have hk4 : k + 2 ≤ 4 := by
    rcases hk with rfl | rfl <;> norm_num
  have hc0 : 0 ≤ (k + 2) / (2 * (n N : ℝ)) :=
    div_nonneg hk0 (by positivity)
  have hc2 : (k + 2) / (2 * (n N : ℝ)) ≤ 2 / (n N : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hn).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hk4) hn.le]
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hterm (i : Fin (n N)) :
      (k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2) ≤
        2 * Real.log 2 / (n N : ℝ) := by
    calc
      _ ≤ (k + 2) / (2 * (n N : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (energy_log_one_add_sq_bounds (hx i)).2 hc0
      _ ≤ (2 / (n N : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hc2 hlog2
      _ = _ := by ring
  constructor
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg hc0 (energy_log_one_add_sq_bounds (hx i)).1)
  · calc
      _ ≤ (1 / (n N : ℝ)) *
          ∑ _i : Fin (n N), (2 * Real.log 2 / (n N : ℝ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) (by positivity)
      _ = 2 * Real.log 2 / (n N : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [hn.ne']

end


end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.CentralCoefficients
namespace OAI

namespace InternalCatalan

section

open scoped BigOperators



@[simp] theorem centralCoeff_zero : centralCoeff 0 = 1 := by
  norm_num [centralCoeff]

@[simp] theorem centralCoeffKernel_zero : centralCoeffKernel 0 = 1 := by
  norm_num [centralCoeffKernel]





@[simp] theorem momentScalar_zero : momentScalar 0 = 2 := by
  norm_num [momentScalar]

theorem momentScalar_even (l : ℕ) :
    momentScalar (2 * l) = 2 / (((2 * l + 1 : ℕ) : ℚ) * centralCoeff l) := by
  simp [momentScalar]

theorem momentScalar_odd (l : ℕ) : momentScalar (2 * l + 1) = 0 := by
  simp [momentScalar]



@[simp] theorem boundaryMinus_zero : boundaryMinus 0 = 0 := rfl
@[simp] theorem boundaryMinus_one : boundaryMinus 1 = 2 := rfl
@[simp] theorem boundaryPlus_zero : boundaryPlus 0 = 0 := rfl
@[simp] theorem boundaryPlus_one : boundaryPlus 1 = 0 := rfl








@[simp] theorem momentRat_zero_right (i : ℕ) : momentRat i 0 = boundaryMinus i := by
  simp [momentRat]

@[simp] theorem momentRat_zero_left (j : ℕ) : momentRat 0 j = boundaryPlus j := by
  cases j with
  | zero => simp [momentRat]
  | succ j => simp [momentRat]






@[simp] theorem harmonicRat_zero (d : ℕ) : harmonicRat d 0 = 0 := by
  simp [harmonicRat]



@[simp] theorem zetaRat_diagonal (i : ℕ) : zetaRat i i = -harmonicRat 2 i := by
  simp [zetaRat]




end

theorem centralCoeff_pos (l : ℕ) : 0 < centralCoeff l := by
  unfold centralCoeff
  apply div_pos
  · exact_mod_cast Nat.centralBinom_pos l
  · positivity

theorem centralCoeff_ne_zero (l : ℕ) : centralCoeff l ≠ 0 :=
  ne_of_gt (centralCoeff_pos l)

theorem centralCoeff_step (l : ℕ) :
    ((2 * l + 2 : ℕ) : ℚ) * centralCoeff (l + 1) =
      ((2 * l + 1 : ℕ) : ℚ) * centralCoeff l := by
  have hc : ((l + 1 : ℕ) : ℚ) * (((2 * (l + 1)).choose (l + 1) : ℕ) : ℚ) =
      2 * ((2 * l + 1 : ℕ) : ℚ) * (((2 * l).choose l : ℕ) : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ l
  have hp : (4 : ℚ) ^ l ≠ 0 := pow_ne_zero l (by norm_num)
  unfold centralCoeff
  rw [pow_succ]
  push_cast at hc ⊢
  field_simp
  nlinarith only [hc]










end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RealColumnDeterminant
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial




@[simp] theorem reversedRow_zero (C : ℕ) : reversedRow C 0 = 0 := by
  simp [reversedRow]



































end

section

open scoped BigOperators









end

section

open Polynomial





theorem polynomial_support_subset_range {F : ℤ[X]} {C : ℕ}
    (hF : F.natDegree < C) : F.support ⊆ Finset.range C := by
  intro i hi
  apply Finset.mem_range.mpr
  exact lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp hi)) hF


variable {K : Type*} [Field K]

theorem reversedRow_eval₂ (f : ℤ →+* K) {C : ℕ} {F : ℤ[X]}
    (hF : F.natDegree < C) {x : K} (hx : x ≠ 0) :
    (reversedRow C F).eval₂ f x = x ^ (C - 1) * F.eval₂ f x⁻¹ := by
  classical
  have hev : F.eval₂ f x⁻¹ =
      ∑ u ∈ Finset.range C, f (F.coeff u) * (x⁻¹) ^ u := by
    rw [eval₂_eq_sum]
    exact sum_eq_of_subset (fun u a => f a * (x⁻¹) ^ u)
      (by intro u; simp) (polynomial_support_subset_range hF)
  rw [hev, Finset.mul_sum]
  unfold reversedRow
  simp only [eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' := Finset.mem_range.mp hu
  have hpow : x ^ (C - 1) = x ^ (C - 1 - u) * x ^ u := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, inv_pow]
  field_simp [hx]

theorem rowP_eval₂ (f : ℤ →+* K) {N r : ℕ} (hN : 0 < N)
    (hr : r < n N) {x : K} (hx : x ≠ 0) :
    (rowP N r).eval₂ f x =
      (1 - x) ^ h N * x ^ (Cdegree N - 1) *
        (Chebyshev.T ℤ (rowDistance N r : ℤ)).eval₂ f x⁻¹ := by
  have hT : (Chebyshev.T ℤ (rowDistance N r : ℤ)).natDegree < Cdegree N := by
    simpa [Chebyshev.natDegree_T] using rowDistance_lt_Cdegree hN hr
  unfold rowP
  rw [eval₂_mul, reversedRow_eval₂ f hT hx]
  simp only [eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  exact (mul_assoc _ _ _).symm

theorem rowD_eval₂ (f : ℤ →+* K) {N r : ℕ} (hN : 0 < N)
    (hr : r < n N) {x : K} (hx : x ≠ 0) :
    (rowD N r).eval₂ f x =
      f (Int.sign (rowOffset N r)) * (1 - x) ^ h N * x ^ (Cdegree N - 1) *
        (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).eval₂ f x⁻¹ := by
  have hU : (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).natDegree < Cdegree N := by
    have hd := rowDistance_lt_Cdegree hN hr
    rw [Chebyshev.natDegree_U]
    simp only [sub_add_cancel, Int.natAbs_natCast]
    omega
  unfold rowD
  rw [eval₂_mul, eval₂_mul, reversedRow_eval₂ f hU hx]
  simp only [eval₂_C, eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  ring

end

open Polynomial

theorem filteredColumn_det_eq_vandermonde (N : ℕ) (s : Fin (n N) → ℝ) :
    Matrix.det (fun j k : Fin (n N) => (filteredColumn N k.val).eval (s j)) =
      Matrix.det (Matrix.vandermonde s) *
        ∏ j : Fin (n N), (s j) ^ b N * (1 - s j) ^ q N := by
  classical
  have hmatrix :
      (fun j k : Fin (n N) => (filteredColumn N k.val).eval (s j)) =
        Matrix.of (fun j k : Fin (n N) =>
          ((s j) ^ b N * (1 - s j) ^ q N) * Matrix.vandermonde s j k) := by
    funext j k
    simp only [filteredColumn, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
      Matrix.of_apply, Matrix.vandermonde_apply, pow_add]
    ring
  rw [hmatrix, Matrix.det_mul_column]
  exact mul_comm _ _

theorem filteredColumn_det_eq_prod (N : ℕ) (s : Fin (n N) → ℝ) :
    Matrix.det (fun j k : Fin (n N) => (filteredColumn N k.val).eval (s j)) =
      (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)) *
        ∏ j : Fin (n N), (s j) ^ b N * (1 - s j) ^ q N := by
  rw [filteredColumn_det_eq_vandermonde, Matrix.det_vandermonde]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.MixedMajorant
namespace OAI

noncomputable section

namespace InternalCatalan

theorem mixed_denominator_rpow_bound {t s : ℝ}
    (ht : |t| < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    (1 - t * s)⁻¹ ≤
      (1 - |t|) ^ (-(1 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) := by
  have hts_abs : t * s ≤ |t| := calc
    t * s ≤ |t| * s := mul_le_mul_of_nonneg_right (le_abs_self t) hs0.le
    _ ≤ |t| := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hs1.le (abs_nonneg t)
  have hts_s : t * s ≤ s := calc
    t * s ≤ 1 * s :=
      mul_le_mul_of_nonneg_right ((le_abs_self t).trans ht.le) hs0.le
    _ = s := one_mul s
  have ha : 0 < 1 - |t| := sub_pos.mpr ht
  have hb : 0 < 1 - s := sub_pos.mpr hs1
  have hDa : 1 - |t| ≤ 1 - t * s := sub_le_sub_left hts_abs 1
  have hDb : 1 - s ≤ 1 - t * s := sub_le_sub_left hts_s 1
  have hD : 0 < 1 - t * s := ha.trans_le hDa
  calc
    (1 - t * s)⁻¹ =
        (1 - t * s) ^ (-(1 / 4) : ℝ) *
          (1 - t * s) ^ (-(3 / 4) : ℝ) := by
      rw [← Real.rpow_add hD,
        show -(1 / 4 : ℝ) + -(3 / 4 : ℝ) = (-1 : ℝ) by norm_num,
        Real.rpow_neg_one]
    _ ≤ (1 - |t|) ^ (-(1 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) :=
      mul_le_mul
        (Real.rpow_le_rpow_of_nonpos ha hDa (by norm_num))
        (Real.rpow_le_rpow_of_nonpos hb hDb (by norm_num))
        (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg ha.le _)

theorem scalar_weight_le_rpow {t : ℝ} (ht : |t| < 1) :
    |t| / Real.sqrt (1 - t ^ 2) ≤ (1 - |t|) ^ (-(1 / 2) : ℝ) := by
  have ht_sq : t ^ 2 ≤ |t| := by
    have hmul := mul_le_mul_of_nonneg_left ht.le (abs_nonneg t)
    nlinarith [sq_abs t]
  have ha : 0 < 1 - |t| := sub_pos.mpr ht
  have haq : 1 - |t| ≤ 1 - t ^ 2 := sub_le_sub_left ht_sq 1
  have hq : 0 < 1 - t ^ 2 := ha.trans_le haq
  calc
    |t| / Real.sqrt (1 - t ^ 2) ≤ 1 / Real.sqrt (1 - t ^ 2) :=
      div_le_div_of_nonneg_right ht.le (Real.sqrt_nonneg _)
    _ = (1 - t ^ 2) ^ (-(1 / 2) : ℝ) := by
      rw [one_div, Real.sqrt_eq_rpow, Real.rpow_neg hq.le]
    _ ≤ (1 - |t|) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos ha haq (by norm_num)

theorem mixed_kernel_norm_le {t s : ℝ} (i j : ℕ)
    (ht : |t| < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    ‖(|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)‖ ≤
      (1 - |t|) ^ (-(3 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) := by
  have ha : 0 < 1 - |t| := sub_pos.mpr ht
  have hts : t * s < 1 := calc
    t * s ≤ |t| * s := mul_le_mul_of_nonneg_right (le_abs_self t) hs0.le
    _ ≤ |t| := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hs1.le (abs_nonneg t)
    _ < 1 := ht
  have hD : 0 < 1 - t * s := sub_pos.mpr hts
  have hw : 0 ≤ |t| / Real.sqrt (1 - t ^ 2) :=
    div_nonneg (abs_nonneg t) (Real.sqrt_nonneg _)
  have hti : |t| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg t) ht.le
  have hsj : s ^ j ≤ 1 := pow_le_one₀ hs0.le hs1.le
  have hm : |t| ^ i * s ^ j ≤ 1 := by
    have h := mul_le_mul hti hsj (pow_nonneg hs0.le j) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using h
  calc
    ‖(|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)‖ =
        ((|t| / Real.sqrt (1 - t ^ 2)) * (|t| ^ i * s ^ j)) *
          (1 - t * s)⁻¹ := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hw,
        abs_mul, abs_pow, abs_pow, abs_of_nonneg hs0.le, abs_of_pos hD,
        div_eq_mul_inv]
    _ ≤ ((|t| / Real.sqrt (1 - t ^ 2)) * 1) * (1 - t * s)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hw)
        (inv_nonneg.mpr hD.le)
    _ = (|t| / Real.sqrt (1 - t ^ 2)) * (1 - t * s)⁻¹ := by rw [mul_one]
    _ ≤ (1 - |t|) ^ (-(1 / 2) : ℝ) *
        ((1 - |t|) ^ (-(1 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ)) :=
      mul_le_mul (scalar_weight_le_rpow ht) (mixed_denominator_rpow_bound ht hs0 hs1)
        (inv_nonneg.mpr hD.le) (Real.rpow_nonneg ha.le _)
    _ = (1 - |t|) ^ (-(3 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) := by
      rw [← mul_assoc, ← Real.rpow_add ha,
        show -(1 / 2 : ℝ) + -(1 / 4 : ℝ) = -(3 / 4 : ℝ) by norm_num]

theorem norm_mixedKernel_le (i j : ℕ) {t s : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)‖ ≤
      (1 - |t|) ^ (-(3 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) :=
  mixed_kernel_norm_le i j (abs_lt.mpr ht) hs.1 hs.2

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.ScalarMomentDecay
namespace OAI

noncomputable section

namespace InternalCatalan

section

open MeasureTheory Set Real
open scoped Interval

def scalarMoment (i : ℕ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, t ^ i * (|t| / Real.sqrt (1 - t ^ 2))

private theorem sine_deriv_nonneg (x : ℝ)
    (hx : x ∈ Ioo (min (-(π / 2)) (π / 2)) (max (-(π / 2)) (π / 2))) :
    0 ≤ cos x := by
  have hp : -(π / 2) ≤ π / 2 := by linarith [pi_pos]
  rw [min_eq_left hp, max_eq_right hp] at hx
  exact (cos_pos_of_mem_Ioo hx).le

private theorem scalar_sine_cancel (i : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    (sin x ^ i * (|sin x| / sqrt (1 - sin x ^ 2))) * cos x =
      sin x ^ i * |sin x| := by
  rw [← cos_eq_sqrt_one_sub_sin_sq hx.1.le hx.2.le]
  have hc : cos x ≠ 0 := (cos_pos_of_mem_Ioo hx).ne'
  field_simp

theorem scalarMoment_eq_sine (i : ℕ) :
    scalarMoment i =
      ∫ x in (-(π / 2))..(π / 2), sin x ^ i * |sin x| := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := -(π / 2)) (b := π / 2) (f := sin) (f' := cos)
    (g := fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
    continuous_sin.continuousOn (fun x _ => hasDerivAt_sin x) sine_deriv_nonneg
  simp only [Function.comp_apply, sin_neg, sin_pi_div_two] at hsub
  unfold scalarMoment
  rw [← hsub]
  apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [pi_pos])
  intro x hx
  exact scalar_sine_cancel i hx

theorem intervalIntegrable_scalarMoment (i : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
      volume (-1) 1 := by
  have hsub := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := -(π / 2)) (b := π / 2) (f := sin) (f' := cos)
    (g := fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
    continuous_sin.continuousOn (fun x _ => hasDerivAt_sin x) sine_deriv_nonneg
  simp only [sin_neg, sin_pi_div_two] at hsub
  apply hsub.mp
  have hc : Continuous (fun x : ℝ => sin x ^ i * |sin x|) := by fun_prop
  apply (hc.intervalIntegrable (-(π / 2)) (π / 2)).congr_uIoo
  intro x hx
  rw [uIoo_of_le (show -(π / 2) ≤ π / 2 by linarith [pi_pos])] at hx
  exact (scalar_sine_cancel i hx).symm

theorem scalarMoment_integrand_odd (k : ℕ) (t : ℝ) :
    (-t) ^ (2 * k + 1) * (|-t| / Real.sqrt (1 - (-t) ^ 2)) =
      -(t ^ (2 * k + 1) * (|t| / Real.sqrt (1 - t ^ 2))) := by
  simp only [abs_neg, neg_sq, pow_add, pow_mul, pow_one]
  ring

theorem scalarMoment_odd (k : ℕ) : scalarMoment (2 * k + 1) = 0 := by
  have h := intervalIntegral.integral_comp_neg
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (fun t : ℝ => t ^ (2 * k + 1) * (|t| / Real.sqrt (1 - t ^ 2)))
  simp only [neg_neg, scalarMoment_integrand_odd, intervalIntegral.integral_neg] at h
  change -scalarMoment (2 * k + 1) = scalarMoment (2 * k + 1) at h
  linarith


private theorem interval_even_double (f : ℝ → ℝ) (hf : Function.Even f) {a : ℝ}
    (hint : IntervalIntegrable f volume (-a) a) (ha : 0 ≤ a) :
    (∫ x in -a..a, f x) = 2 * ∫ x in (0 : ℝ)..a, f x := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (-a) a := by
    rw [Set.uIcc_of_le (by linarith : -a ≤ a)]
    exact ⟨by linarith, ha⟩
  obtain ⟨hl, hr⟩ := (IntervalIntegrable.trans_iff h0).mp hint
  have hf' (x : ℝ) : f (-x) = f x := hf x
  have hleft : (∫ x in -a..0, f x) = ∫ x in (0 : ℝ)..a, f x := by
    simpa only [hf', neg_zero] using
      (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := a) f).symm
  calc
    (∫ x in -a..a, f x) = (∫ x in -a..0, f x) + ∫ x in (0 : ℝ)..a, f x :=
      (intervalIntegral.integral_add_adjacent_intervals hl hr).symm
    _ = 2 * ∫ x in (0 : ℝ)..a, f x := by rw [hleft]; ring

theorem scalarMoment_even_eq_sine (l : ℕ) :
    scalarMoment (2 * l) =
      2 * (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1)) := by
  rw [scalarMoment_eq_sine]
  have hf : Function.Even (fun x : ℝ => sin x ^ (2 * l) * |sin x|) := by
    intro x
    simp only [sin_neg, abs_neg, pow_mul, neg_sq]
  have hc : Continuous (fun x : ℝ => sin x ^ (2 * l) * |sin x|) := by fun_prop
  rw [interval_even_double _ hf (hc.intervalIntegrable (-(π / 2)) (π / 2)) (by positivity)]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
  intro x hx
  have hs : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx.1.le (by linarith [hx.2, pi_pos])
  change sin x ^ (2 * l) * |sin x| = sin x ^ (2 * l + 1)
  rw [abs_of_nonneg hs, pow_succ]

theorem two_integral_sine_odd_eq_momentScalar (l : ℕ) :
    2 * (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1)) =
      (momentScalar (2 * l) : ℝ) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have he : 2 * (l + 1) + 1 = (2 * l + 1) + 2 := by omega
    have hrec := integral_sin_pow (a := 0) (b := π / 2) (2 * l + 1)
    have hexp : 0 < 2 * l + 1 + 1 := by omega
    simp only [sin_zero, zero_pow (Nat.ne_of_gt hexp), cos_zero, zero_mul,
      sin_pi_div_two, one_pow, cos_pi_div_two, mul_zero, sub_self, zero_div,
      zero_add] at hrec
    rw [he, hrec]
    rw [show 2 * ((↑(2 * l + 1) + 1) / (↑(2 * l + 1) + 2) *
      (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1))) =
        ((↑(2 * l + 1) + 1) / (↑(2 * l + 1) + 2)) *
          (2 * (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1))) by ring, ih]
    rw [momentScalar_even, momentScalar_even]
    have hc : (↑(2 * l + 2) : ℝ) * (centralCoeff (l + 1) : ℝ) =
        (↑(2 * l + 1) : ℝ) * (centralCoeff l : ℝ) := by
      exact_mod_cast centralCoeff_step l
    have hc0 : (centralCoeff l : ℝ) ≠ 0 := by
      exact_mod_cast centralCoeff_ne_zero l
    have hc1 : (centralCoeff (l + 1) : ℝ) ≠ 0 := by
      exact_mod_cast centralCoeff_ne_zero (l + 1)
    push_cast at hc ⊢
    field_simp
    nlinarith only [hc]

theorem scalarMoment_eq_momentScalar (i : ℕ) :
    scalarMoment i = (momentScalar i : ℝ) := by
  rcases Nat.even_or_odd' i with ⟨l, rfl | rfl⟩
  · exact (scalarMoment_even_eq_sine l).trans
      (two_integral_sine_odd_eq_momentScalar l)
  · rw [scalarMoment_odd, momentScalar_odd, Rat.cast_zero]

@[simp] theorem scalarMoment_zero : scalarMoment 0 = 2 := by
  rw [scalarMoment_eq_momentScalar, momentScalar_zero]
  norm_num

end

open MeasureTheory Set Real Filter
open scoped Interval Topology



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.MixedSeries
namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set Real Polynomial

private theorem intervalIntegrable_one_sub_rpow :
    IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(3 / 4) : ℝ)) volume 0 1 := by
  have h := intervalIntegral.intervalIntegrable_rpow'
    (a := (0 : ℝ)) (b := 1) (r := -(3 / 4)) (by norm_num)
  simpa only [sub_zero, sub_self] using (h.comp_sub_left 1).symm

private theorem intervalIntegrable_one_sub_abs_rpow :
    IntervalIntegrable (fun t : ℝ => (1 - |t|) ^ (-(3 / 4) : ℝ)) volume (-1) 1 := by
  have hp : IntervalIntegrable (fun t : ℝ => (1 - |t|) ^ (-(3 / 4) : ℝ))
      volume 0 1 := by
    apply intervalIntegrable_one_sub_rpow.congr_uIoo
    intro t ht
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [abs_of_pos ht.1]
  have hn : IntervalIntegrable (fun t : ℝ => (1 - |t|) ^ (-(3 / 4) : ℝ))
      volume (-1) 0 := by
    simpa only [zero_sub, sub_zero, abs_neg] using (hp.comp_sub_left 0).symm
  exact hn.trans hp

theorem integrable_mixedMajorant :
    Integrable (fun p : ℝ × ℝ =>
      (1 - |p.1|) ^ (-(3 / 4) : ℝ) * (1 - p.2) ^ (-(3 / 4) : ℝ))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have ht := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).mp intervalIntegrable_one_sub_abs_rpow
  have hs := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mp intervalIntegrable_one_sub_rpow
  exact ht.mul_prod hs

theorem ae_mem_mixed_rectangle :
    ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1)),
      p ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact ⟨ht, hs⟩

theorem integrable_mixedKernel (i j : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2)) := by
    fun_prop
  apply integrable_mixedMajorant.mono' hm.aestronglyMeasurable
  filter_upwards [ae_mem_mixed_rectangle] with p hp
  exact norm_mixedKernel_le i j hp.1 hp.2

theorem mixedMoment_X_pow_eq_integral_prod (i j : ℕ) :
    mixedMoment (X ^ i) (X ^ j) =
      ∫ p : ℝ × ℝ,
        (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2)
        ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have h := integral_prod
    (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2))
    (integrable_mixedKernel i j)
  simpa only [mixedMoment, Polynomial.eval_pow, Polynomial.eval_X,
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h.symm



open MeasureTheory Set Real Polynomial
open scoped BigOperators Topology




end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.RealEnergyLogSeries
namespace OAI

noncomputable section
open Set

namespace InternalCatalan


theorem energy_hasSum_re_power_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (z ^ k).re / (k : ℝ))
      (-Real.log ‖1 - z‖) := by
  simpa only [Complex.div_natCast_re, Complex.neg_re, Complex.log_re] using
    Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz)




theorem energy_hasSum_real_power_div {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u ^ k / (k : ℝ)) (-Real.log (1 - u)) := by
  have huNorm : ‖(u : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_lt.mpr hu
  have hnorm : ‖(1 : ℂ) - (u : ℂ)‖ = 1 - u := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hu.2)]
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, hnorm] using
    energy_hasSum_re_power_div huNorm



theorem energy_mul_mem_Ioo {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    x * y ∈ Ioo (-1 : ℝ) 1 := by
  apply abs_lt.mp
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left (abs_lt.mpr hy).le (abs_nonneg x)
    _ < 1 := by simpa only [mul_one] using abs_lt.mpr hx

theorem energy_hasSum_mul_power_div {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => (x * y) ^ k / (k : ℝ))
      (-Real.log (1 - x * y)) :=
  energy_hasSum_real_power_div (energy_mul_mem_Ioo hx hy)


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealEnergyChebyshev
namespace OAI

noncomputable section

namespace InternalCatalan

section

theorem energy_chord_sq_identity (ζ : ℂ) (hζ : ‖ζ‖ = 1) (r : ℝ) :
    ‖(1 : ℂ) - (r : ℂ) * ζ‖ ^ 2 - r * ‖(1 : ℂ) - ζ‖ ^ 2 = (1 - r) ^ 2 := by
  have hζsq : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hζ, one_pow]
  simp only [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one,
    Complex.normSq_mul, Complex.normSq_ofReal, hζsq, one_mul, mul_one,
    Complex.conj_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

theorem energy_chord_sq_le (ζ : ℂ) (hζ : ‖ζ‖ = 1) (r : ℝ) :
    r * ‖(1 : ℂ) - ζ‖ ^ 2 ≤ ‖(1 : ℂ) - (r : ℂ) * ζ‖ ^ 2 := by
  have hid := energy_chord_sq_identity ζ hζ r
  nlinarith [sq_nonneg (1 - r)]

theorem energy_damped_chord_pos (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1)
    {r : ℝ} (hr : 0 < r) : 0 < ‖(1 : ℂ) - (r : ℂ) * ζ‖ := by
  have horig : 0 < ‖(1 : ℂ) - ζ‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hζ1.symm)
  have hsquare : 0 < ‖(1 : ℂ) - (r : ℂ) * ζ‖ ^ 2 :=
    lt_of_lt_of_le (mul_pos hr (sq_pos_of_pos horig)) (energy_chord_sq_le ζ hζ r)
  nlinarith [norm_nonneg ((1 : ℂ) - (r : ℂ) * ζ)]

theorem energy_log_chord_le (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1)
    {r : ℝ} (hr : 0 < r) :
    Real.log ‖(1 : ℂ) - ζ‖ ≤
      Real.log ‖(1 : ℂ) - (r : ℂ) * ζ‖ - Real.log r / 2 := by
  have horig : 0 < ‖(1 : ℂ) - ζ‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hζ1.symm)
  have hdamped := energy_damped_chord_pos ζ hζ hζ1 hr
  have hlog := (Real.log_le_log_iff (mul_pos hr (sq_pos_of_pos horig))
    (sq_pos_of_pos hdamped)).mpr (energy_chord_sq_le ζ hζ r)
  rw [Real.log_mul hr.ne' (pow_ne_zero 2 horig.ne')] at hlog
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog
  linarith

end

section

open Set
open scoped ComplexConjugate

def realEnergyCirclePoint (u : ℝ) : ℂ :=
  (u : ℂ) + Complex.I * (Real.sqrt (1 - u ^ 2) : ℂ)

theorem realEnergyCirclePoint_norm {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    ‖realEnergyCirclePoint u‖ = 1 := by
  have hn : ‖u‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using abs_le.mpr hu
  have h := Complex.normSq_ofReal_add_I_mul_sqrt_one_sub hn
  change Complex.normSq (realEnergyCirclePoint u) = 1 at h
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (realEnergyCirclePoint u)]

theorem realEnergyCirclePoint_add_conj (u : ℝ) :
    realEnergyCirclePoint u + conj (realEnergyCirclePoint u) = 2 * (u : ℂ) := by
  apply Complex.ext <;> simp [realEnergyCirclePoint]
  ring

theorem realEnergyCirclePoint_mul_conj {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    realEnergyCirclePoint u * conj (realEnergyCirclePoint u) = 1 := by
  rw [Complex.mul_conj', realEnergyCirclePoint_norm hu]
  norm_num

theorem realEnergyCirclePoint_quadratic {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    realEnergyCirclePoint u ^ 2 + 1 = 2 * (u : ℂ) * realEnergyCirclePoint u := by
  calc
    _ = realEnergyCirclePoint u *
        (realEnergyCirclePoint u + conj (realEnergyCirclePoint u)) := by
      rw [mul_add, realEnergyCirclePoint_mul_conj hu, pow_two]
    _ = _ := by rw [realEnergyCirclePoint_add_conj]; ring

theorem realEnergy_cosine_chord_product {u v : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    ‖(1 : ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v‖ *
      ‖(1 : ℂ) - realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ =
      2 * |u - v| := by
  have hc :
      ((1 : ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v) *
        ((1 : ℂ) - realEnergyCirclePoint u * conj (realEnergyCirclePoint v)) =
      2 * realEnergyCirclePoint u * ((u : ℂ) - (v : ℂ)) := by
    calc
      _ = 1 - realEnergyCirclePoint u *
          (realEnergyCirclePoint v + conj (realEnergyCirclePoint v)) +
          realEnergyCirclePoint u ^ 2 *
            (realEnergyCirclePoint v * conj (realEnergyCirclePoint v)) := by ring
      _ = (realEnergyCirclePoint u ^ 2 + 1) -
          2 * (v : ℂ) * realEnergyCirclePoint u := by
        rw [realEnergyCirclePoint_add_conj, realEnergyCirclePoint_mul_conj hv]
        ring
      _ = _ := by rw [realEnergyCirclePoint_quadratic hu]; ring
  have hh := congrArg (fun z : ℂ => ‖z‖) hc
  simpa only [Complex.norm_mul, realEnergyCirclePoint_norm hu,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, mul_one] using hh

def realEnergyCosineKernel (r u v : ℝ) : ℝ :=
  -Real.log 2 +
    Real.log ‖(1 : ℂ) - (r : ℂ) * (realEnergyCirclePoint u * realEnergyCirclePoint v)‖ +
    Real.log ‖(1 : ℂ) - (r : ℂ) * (realEnergyCirclePoint u * conj (realEnergyCirclePoint v))‖

theorem realEnergyCosineKernel_one {u v : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) (huv : u ≠ v) :
    realEnergyCosineKernel 1 u v = Real.log |u - v| := by
  have hp := realEnergy_cosine_chord_product hu hv
  have hprod :
      ‖(1 : ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v‖ *
        ‖(1 : ℂ) - realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ ≠ 0 := by
    rw [hp]
    exact mul_ne_zero (by norm_num) (abs_ne_zero.mpr (sub_ne_zero.mpr huv))
  have hl := congrArg Real.log hp
  rw [Real.log_mul (mul_ne_zero_iff.mp hprod).1 (mul_ne_zero_iff.mp hprod).2,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (abs_ne_zero.mpr (sub_ne_zero.mpr huv))] at hl
  unfold realEnergyCosineKernel
  simp only [Complex.ofReal_one, one_mul]
  linarith

theorem realEnergyCosineKernel_compare {u v r : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1)
    (huv : u ≠ v) (hr : 0 < r) :
    Real.log |u - v| ≤ realEnergyCosineKernel r u v - Real.log r := by
  have hp := realEnergy_cosine_chord_product hu hv
  have hprod :
      ‖(1 : ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v‖ *
        ‖(1 : ℂ) - realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ ≠ 0 := by
    rw [hp]
    exact mul_ne_zero (by norm_num) (abs_ne_zero.mpr (sub_ne_zero.mpr huv))
  have hn1 : ‖realEnergyCirclePoint u * realEnergyCirclePoint v‖ = 1 := by
    rw [Complex.norm_mul, realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have hn2 : ‖realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ = 1 := by
    rw [Complex.norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have hne1 : realEnergyCirclePoint u * realEnergyCirclePoint v ≠ 1 := by
    intro h
    apply (mul_ne_zero_iff.mp hprod).1
    rw [h, sub_self, norm_zero]
  have hne2 : realEnergyCirclePoint u * conj (realEnergyCirclePoint v) ≠ 1 := by
    intro h
    apply (mul_ne_zero_iff.mp hprod).2
    rw [h, sub_self, norm_zero]
  have h1 := energy_log_chord_le _ hn1 hne1 hr
  have h2 := energy_log_chord_le _ hn2 hne2 hr
  rw [← realEnergyCosineKernel_one hu hv huv]
  unfold realEnergyCosineKernel
  simp only [Complex.ofReal_one, one_mul]
  linarith

end

open Polynomial Set
open scoped ComplexConjugate

theorem realEnergyCirclePoint_pow_re (k : ℕ) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    (realEnergyCirclePoint u ^ k).re = (Chebyshev.T ℝ (k : ℤ)).eval u := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp [realEnergyCirclePoint]
  | more k ih0 ih1 =>
    have hp : realEnergyCirclePoint u ^ (k + 2) + realEnergyCirclePoint u ^ k =
        2 * (u : ℂ) * realEnergyCirclePoint u ^ (k + 1) := by
      calc
        _ = realEnergyCirclePoint u ^ k * (realEnergyCirclePoint u ^ 2 + 1) := by
          rw [pow_add]
          ring
        _ = _ := by
          rw [realEnergyCirclePoint_quadratic hu, pow_succ]
          ring
    have hr := congrArg Complex.re hp
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero, add_zero] at hr
    have hi1 : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
    rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    rw [hi1, ← ih1, ← ih0]
    linarith

theorem energy_chebyshev_abs_le_one (k : ℕ) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) : |(Chebyshev.T ℝ (k : ℤ)).eval u| ≤ 1 := by
  rw [← realEnergyCirclePoint_pow_re k hu]
  calc
    _ ≤ ‖realEnergyCirclePoint u ^ k‖ := Complex.abs_re_le_norm _
    _ = 1 := by rw [Complex.norm_pow, realEnergyCirclePoint_norm hu, one_pow]

theorem realEnergyCirclePoint_pair_pow_re (k : ℕ) {u v : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    ((realEnergyCirclePoint u * realEnergyCirclePoint v) ^ k).re +
      ((realEnergyCirclePoint u * conj (realEnergyCirclePoint v)) ^ k).re =
      2 * (Chebyshev.T ℝ (k : ℤ)).eval u * (Chebyshev.T ℝ (k : ℤ)).eval v := by
  simp only [mul_pow, ← map_pow, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [realEnergyCirclePoint_pow_re k hu, realEnergyCirclePoint_pow_re k hv]
  ring

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.RealEnergyKernelSeries
namespace OAI

noncomputable section
open Polynomial Set
open scoped ComplexConjugate

namespace InternalCatalan

theorem energy_scaled_pow_re (a : ℝ) (z : ℂ) (k : ℕ) :
    (((a : ℂ) * z) ^ k).re = a ^ k * (z ^ k).re := by
  simp only [mul_pow, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem energy_hasSum_cosine_kernel {r u v : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ =>
      2 * r ^ k * (Chebyshev.T ℝ (k : ℤ)).eval u * (Chebyshev.T ℝ (k : ℤ)).eval v /
        (k : ℝ)) (-realEnergyCosineKernel r u v - Real.log 2) := by
  have hn1 : ‖(r : ℂ) * (realEnergyCirclePoint u * realEnergyCirclePoint v)‖ < 1 := by
    simpa only [Complex.norm_mul, realEnergyCirclePoint_norm hu,
      realEnergyCirclePoint_norm hv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr.1, mul_one] using hr.2
  have hn2 : ‖(r : ℂ) * (realEnergyCirclePoint u * conj (realEnergyCirclePoint v))‖ < 1 := by
    simpa only [Complex.norm_mul, Complex.norm_conj, realEnergyCirclePoint_norm hu,
      realEnergyCirclePoint_norm hv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr.1, mul_one] using hr.2
  have h1 := energy_hasSum_re_power_div hn1
  have h2 := energy_hasSum_re_power_div hn2
  convert h1.add h2 using 1
  · ext k
    rw [energy_scaled_pow_re, energy_scaled_pow_re]
    have hp := realEnergyCirclePoint_pair_pow_re k hu hv
    calc
      _ = r ^ k *
          (((realEnergyCirclePoint u * realEnergyCirclePoint v) ^ k).re +
            ((realEnergyCirclePoint u * conj (realEnergyCirclePoint v)) ^ k).re) / (k : ℝ) := by
        rw [hp]
        ring
      _ = _ := by ring
  · unfold realEnergyCosineKernel
    ring


theorem realEnergy_circle_scaled_chord_sq (x : ℝ) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    ‖(1 : ℂ) - (x : ℂ) * realEnergyCirclePoint s‖ ^ 2 = 1 - 2 * x * s + x ^ 2 := by
  have hsq : Complex.normSq (realEnergyCirclePoint s) = 1 := by
    rw [Complex.normSq_eq_norm_sq, realEnergyCirclePoint_norm hs, one_pow]
  have hre : (realEnergyCirclePoint s).re = s := by simp [realEnergyCirclePoint]
  simp only [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one,
    Complex.normSq_mul, Complex.normSq_ofReal, hsq, one_mul, mul_one,
    Complex.conj_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hre]
  ring

theorem energy_hasSum_cross_kernel {x s : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => 2 * x ^ k * (Chebyshev.T ℝ (k : ℤ)).eval s / (k : ℝ))
      (-Real.log (1 - 2 * x * s + x ^ 2)) := by
  have hz : ‖(x : ℂ) * realEnergyCirclePoint s‖ < 1 := by
    simpa only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      realEnergyCirclePoint_norm hs, mul_one] using abs_lt.mpr hx
  have hh := (energy_hasSum_re_power_div hz).mul_left (2 : ℝ)
  have hl : Real.log (1 - 2 * x * s + x ^ 2) =
      2 * Real.log ‖(1 : ℂ) - (x : ℂ) * realEnergyCirclePoint s‖ := by
    rw [← realEnergy_circle_scaled_chord_sq x hs, Real.log_pow]
    norm_num
  convert hh using 1
  all_goals first
    | rfl
    | (ext k
       rw [energy_scaled_pow_re, realEnergyCirclePoint_pow_re k hs]
       ring)
    | (rw [hl]
       ring)


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.ZetaIntegral
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Filter
open scoped BigOperators Topology

def zetaTerm (i j u : ℕ) : ℝ :=
  1 / (((i + u + 1 : ℕ) : ℝ) * ((j + u + 1 : ℕ) : ℝ))

def zetaSeries (i j : ℕ) : ℝ := ∑' u : ℕ, zetaTerm i j u

theorem zetaTerm_nonneg (i j u : ℕ) : 0 ≤ zetaTerm i j u := by
  unfold zetaTerm
  positivity

theorem zetaTerm_le_inverse_square (i j u : ℕ) :
    zetaTerm i j u ≤ 1 / ((u + 1 : ℕ) : ℝ) ^ 2 := by
  unfold zetaTerm
  apply one_div_le_one_div_of_le (by positivity)
  have hi : ((u + 1 : ℕ) : ℝ) ≤ ((i + u + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show u + 1 ≤ i + u + 1 by omega)
  have hj : ((u + 1 : ℕ) : ℝ) ≤ ((j + u + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show u + 1 ≤ j + u + 1 by omega)
  simpa only [pow_two] using
    mul_le_mul hi hj (by positivity) (by positivity)

theorem summable_inverse_square_succ :
    Summable (fun u : ℕ => 1 / ((u + 1 : ℕ) : ℝ) ^ 2) := by
  have h : Summable (fun u : ℕ => 1 / (u : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
  exact h.comp_injective (show Function.Injective (fun u : ℕ => u + 1) by
    intro a b hab
    change a + 1 = b + 1 at hab
    omega)

theorem summable_zetaTerm (i j : ℕ) : Summable (zetaTerm i j) := by
  apply summable_inverse_square_succ.of_norm_bounded
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (zetaTerm_nonneg i j u)]
  exact zetaTerm_le_inverse_square i j u




theorem zetaSeries_nonneg (i j : ℕ) : 0 ≤ zetaSeries i j :=
  tsum_nonneg (zetaTerm_nonneg i j)


theorem zetaTerm_shift (i j u m : ℕ) :
    zetaTerm i j (u + m) = zetaTerm (i + m) (j + m) u := by
  simp only [zetaTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem zetaSeries_split (i j m : ℕ) :
    (∑ u ∈ Finset.range m, zetaTerm i j u) + zetaSeries (i + m) (j + m) =
      zetaSeries i j := by
  have h := (summable_zetaTerm i j).sum_add_tsum_nat_add m
  simpa only [zetaTerm_shift, zetaSeries] using h

theorem zetaSeries_step (i j : ℕ) :
    zetaSeries i j - zetaSeries (i + 1) (j + 1) =
      1 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
  have h := zetaSeries_split i j 1
  simp only [Finset.sum_range_one, zetaTerm, Nat.add_zero] at h
  linarith




end

section

open Filter
open scoped Topology







end

section

open MeasureTheory
open scoped BigOperators Topology

theorem hasSum_zetaKernel (i j : ℕ) {t s : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun u : ℕ => t ^ (i + u) * s ^ (j + u))
      (t ^ i * s ^ j / (1 - t * s)) := by
  have hts : |t * s| < 1 := by
    rw [abs_of_nonneg (mul_nonneg ht.1.le hs.1.le)]
    have hmul : t * s < t := by nlinarith [ht.1, hs.2]
    exact hmul.trans ht.2
  convert (hasSum_geometric_of_abs_lt_one hts).mul_left (t ^ i * s ^ j) using 1
  · rfl
  · ext u
    simp only [pow_add, mul_pow]
    ring
  · rfl

theorem integrableOn_pow_unit (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k) (Set.Ioo (0 : ℝ) 1) := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
  exact (continuous_id.pow k).intervalIntegrable 0 1

theorem integrable_zetaMonomial (i j u : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ (i + u) * p.2 ^ (j + u))
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) 1))) :=
  (integrableOn_pow_unit (i + u)).mul_prod (integrableOn_pow_unit (j + u))

theorem integral_zetaMonomial (i j u : ℕ) :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
      t ^ (i + u) * s ^ (j + u)) = zetaTerm i j u := by
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_pow, one_pow, zero_pow (Nat.add_one_ne_zero _),
    sub_zero, zetaTerm, Nat.cast_add, Nat.cast_one]
  simp only [one_div, mul_inv_rev]
  ring

end

section

open MeasureTheory Set
open scoped BigOperators Topology












end

open MeasureTheory Set Polynomial
open scoped BigOperators Topology

private theorem ae_mem_unit_square :
    ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1)),
      p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact ⟨ht, hs⟩

theorem integral_prod_zetaKernel (i j : ℕ) :
    (∫ p : ℝ × ℝ, p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) = zetaSeries i j := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : ℕ → ℝ × ℝ → ℝ := fun u p => p.1 ^ (i + u) * p.2 ^ (j + u)
  have hF : ∀ u, Integrable (F u) (μ.prod μ) := fun u =>
    integrable_zetaMonomial i j u
  have hterm (u : ℕ) : (∫ p, F u p ∂μ.prod μ) = zetaTerm i j u := by
    rw [integral_prod _ (hF u)]
    simpa only [μ, F, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      integral_Ioc_eq_integral_Ioo] using integral_zetaMonomial i j u
  have hnorm (u : ℕ) : (∫ p, ‖F u p‖ ∂μ.prod μ) = zetaTerm i j u := by
    rw [← hterm u]
    apply integral_congr_ae
    filter_upwards [ae_mem_unit_square] with p hp
    exact Real.norm_of_nonneg
      (mul_nonneg (pow_nonneg hp.1.1.le _) (pow_nonneg hp.2.1.le _))
  have hsum : Summable (fun u => ∫ p, ‖F u p‖ ∂μ.prod μ) := by
    simpa only [hnorm] using summable_zetaTerm i j
  have hinterchange := integral_tsum_of_summable_integral_norm hF hsum
  have hgeom : (fun p => ∑' u, F u p) =ᵐ[μ.prod μ]
      (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2)) := by
    filter_upwards [ae_mem_unit_square] with p hp
    exact (hasSum_zetaKernel i j hp.1 hp.2).tsum_eq
  calc
    (∫ p : ℝ × ℝ, p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2) ∂μ.prod μ) =
        ∫ p, (∑' u, F u p) ∂μ.prod μ := integral_congr_ae hgeom.symm
    _ = ∑' u, ∫ p, F u p ∂μ.prod μ := hinterchange.symm
    _ = zetaSeries i j := by simp only [hterm, zetaSeries]

theorem integrable_zetaKernel (i j : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_prod_zetaKernel]
  have hstep := zetaSeries_step i j
  have htail := zetaSeries_nonneg (i + 1) (j + 1)
  have hzero : 0 < 1 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) := by positivity
  have hpos : 0 < zetaSeries i j := by linarith
  exact hpos.ne'



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.MixedOneStart
namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set Real




open MeasureTheory Set Real Polynomial
open scoped Interval

theorem mixed_affine_denominator_pos {t s : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) : 0 < 1 - t * s := by
  by_cases ht0 : 0 ≤ t
  · have hts : t * s ≤ t := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hs.2)]
    linarith [ht.2]
  · have hts : t * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht0) hs.1
    linarith






open MeasureTheory Set Real Polynomial
open scoped Interval




end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RealRowAmplitude
namespace OAI

noncomputable section

open Set Polynomial

namespace InternalCatalan

def realRowAmplitude (N r : ℕ) (t : ℝ) : ℝ :=
  (realPoly (rowP N r)).eval t - (3 / 2 : ℝ) *
    (if 0 < t then Real.sqrt (1 - t ^ 2) / t * (realPoly (rowD N r)).eval t else 0)

theorem realRowAmplitude_of_nonpos (N r : ℕ) {t : ℝ} (ht : t ≤ 0) :
    realRowAmplitude N r t = (realPoly (rowP N r)).eval t := by
  simp [realRowAmplitude, not_lt.mpr ht]

theorem realRowAmplitude_of_neg (N r : ℕ) {t : ℝ} (ht : t < 0) :
    realRowAmplitude N r t = (realPoly (rowP N r)).eval t :=
  realRowAmplitude_of_nonpos N r ht.le

theorem realRowAmplitude_of_pos (N r : ℕ) {t : ℝ} (ht : 0 < t) :
    realRowAmplitude N r t = (realPoly (rowP N r)).eval t -
      (3 / 2 : ℝ) * (Real.sqrt (1 - t ^ 2) / t * (realPoly (rowD N r)).eval t) := by
  simp [realRowAmplitude, ht]

theorem realRowAmplitude_weighted_eq (N r : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (|t| / Real.sqrt (1 - t ^ 2)) * realRowAmplitude N r t =
      (|t| / Real.sqrt (1 - t ^ 2)) * (realPoly (rowP N r)).eval t -
        (3 / 2 : ℝ) * (if 0 < t then (realPoly (rowD N r)).eval t else 0) := by
  by_cases hp : 0 < t
  · rw [realRowAmplitude_of_pos N r hp, if_pos hp]
    have ht0 : t ≠ 0 := hp.ne'
    have hrad : 0 < 1 - t ^ 2 := by
      have hprod := mul_pos (sub_pos.mpr ht.2) (show (0 : ℝ) < 1 + t by linarith [ht.1])
      nlinarith
    have hs0 : Real.sqrt (1 - t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr hrad).ne'
    have hcancel :
        (|t| / Real.sqrt (1 - t ^ 2)) * (Real.sqrt (1 - t ^ 2) / t) = 1 := by
      rw [abs_of_pos hp]
      field_simp [ht0, hs0]
    calc
      _ = (|t| / Real.sqrt (1 - t ^ 2)) * (realPoly (rowP N r)).eval t -
          (3 / 2 : ℝ) *
            (((|t| / Real.sqrt (1 - t ^ 2)) * (Real.sqrt (1 - t ^ 2) / t)) *
              (realPoly (rowD N r)).eval t) := by ring
      _ = _ := by rw [hcancel]; ring
  · rw [realRowAmplitude_of_nonpos N r (le_of_not_gt hp), if_neg hp]
    simp

theorem realRowAmplitude_kernel_eq (N r : ℕ) (Q : ℝ[X]) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (s : ℝ) :
    (|t| / Real.sqrt (1 - t ^ 2)) * (realRowAmplitude N r t * Q.eval s) /
        (1 - t * s) =
      (|t| / Real.sqrt (1 - t ^ 2)) * ((realPoly (rowP N r)).eval t * Q.eval s) /
          (1 - t * s) -
        (3 / 2 : ℝ) *
          (if 0 < t then (realPoly (rowD N r)).eval t * Q.eval s / (1 - t * s)
            else 0) := by
  calc
    _ = ((|t| / Real.sqrt (1 - t ^ 2)) * realRowAmplitude N r t) * Q.eval s /
        (1 - t * s) := by ring
    _ = ((|t| / Real.sqrt (1 - t ^ 2)) * (realPoly (rowP N r)).eval t -
        (3 / 2 : ℝ) * (if 0 < t then (realPoly (rowD N r)).eval t else 0)) *
          Q.eval s / (1 - t * s) := by rw [realRowAmplitude_weighted_eq N r ht]
    _ = _ := by
      by_cases hp : 0 < t
      · simp only [if_pos hp]
        ring
      · simp only [if_neg hp]
        ring

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealEnergyDiagonal
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Set Real


def realCoordinateInv (x : ℝ) : ℝ := 2 * x / (1 + x ^ 2)

private theorem coordinate_radicand_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - x ^ 2 := by
  have hsq : x ^ 2 < 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_lt_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)).mpr (abs_lt.mpr hx)
  linarith

theorem realCoordinateInv_mem {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    realCoordinateInv x ∈ Ioo (-1 : ℝ) 1 := by
  have hd : 0 < 1 + x ^ 2 := by positivity
  constructor
  · unfold realCoordinateInv
    apply (lt_div_iff₀ hd).mpr
    nlinarith [sq_pos_of_ne_zero (by linarith [hx.1] : x + 1 ≠ 0)]
  · unfold realCoordinateInv
    apply (div_lt_iff₀ hd).mpr
    nlinarith [sq_pos_of_ne_zero (by linarith [hx.2] : x - 1 ≠ 0)]

theorem sqrt_one_sub_realCoordinateInv_sq {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    sqrt (1 - realCoordinateInv x ^ 2) = (1 - x ^ 2) / (1 + x ^ 2) := by
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have hsq : 1 - realCoordinateInv x ^ 2 =
      ((1 - x ^ 2) / (1 + x ^ 2)) ^ 2 := by
    unfold realCoordinateInv
    field_simp
    ring
  rw [hsq, sqrt_sq (div_nonneg (coordinate_radicand_pos hx).le (by positivity))]





theorem hasDerivAt_realCoordinateInv (x : ℝ) :
    HasDerivAt realCoordinateInv (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) x := by
  have h := ((hasDerivAt_id x).const_mul 2).div
    ((hasDerivAt_pow 2 x).const_add 1) (by positivity : 1 + x ^ 2 ≠ 0)
  have heq : ((fun y : ℝ => 2 * id y) / (fun y : ℝ => 1 + y ^ 2)) =
      realCoordinateInv := by
    funext y
    rfl
  rw [heq] at h
  have hd : (2 * 1 * (1 + x ^ 2) - 2 * id x * (((2 : ℕ) : ℝ) * x ^ (2 - 1))) /
      (1 + x ^ 2) ^ 2 = 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2 := by
    norm_num
    ring
  rw [hd] at h
  exact h

theorem continuous_realCoordinateInv : Continuous realCoordinateInv :=
  (continuous_const.mul continuous_id).div
    (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)

theorem realCoordinate_weight_jacobian {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (|realCoordinateInv x| / sqrt (1 - realCoordinateInv x ^ 2)) *
        (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) =
      4 * |x| / (1 + x ^ 2) ^ 2 := by
  rw [sqrt_one_sub_realCoordinateInv_sq hx]
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have hr : 1 - x ^ 2 ≠ 0 := (coordinate_radicand_pos hx).ne'
  unfold realCoordinateInv
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by positivity : 0 < 1 + x ^ 2)]
  field_simp
  ring

end

section

open Set

section

theorem realCoordinateInv_denominator_pos (x : ℝ) : 0 < 1 + x ^ 2 := by
  positivity

theorem abs_realCoordinateInv (x : ℝ) :
    |realCoordinateInv x| = 2 * |x| / (1 + x ^ 2) := by
  unfold realCoordinateInv
  simp only [abs_div, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (realCoordinateInv_denominator_pos x)]

theorem realCoordinateInv_sub (x y : ℝ) :
    realCoordinateInv x - realCoordinateInv y =
      2 * (x - y) * (1 - x * y) / ((1 + x ^ 2) * (1 + y ^ 2)) := by
  have hx : 1 + x ^ 2 ≠ 0 := (realCoordinateInv_denominator_pos x).ne'
  have hy : 1 + y ^ 2 ≠ 0 := (realCoordinateInv_denominator_pos y).ne'
  unfold realCoordinateInv
  field_simp [hx, hy]
  ring

theorem energy_one_sub_mul_pos {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - x * y := by
  apply sub_pos.mpr
  calc
    x * y ≤ |x * y| := le_abs_self _
    _ = |x| * |y| := abs_mul x y
    _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left (abs_lt.mpr hy).le (abs_nonneg x)
    _ = |x| := mul_one _
    _ < 1 := abs_lt.mpr hx

theorem abs_realCoordinateInv_sub {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    |realCoordinateInv x - realCoordinateInv y| =
      2 * |x - y| * (1 - x * y) / ((1 + x ^ 2) * (1 + y ^ 2)) := by
  rw [realCoordinateInv_sub]
  simp only [abs_div, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (energy_one_sub_mul_pos hx hy),
    abs_of_pos (realCoordinateInv_denominator_pos x),
    abs_of_pos (realCoordinateInv_denominator_pos y)]

theorem one_sub_realCoordinateInv_mul (x s : ℝ) :
    1 - realCoordinateInv x * s = (1 - 2 * x * s + x ^ 2) / (1 + x ^ 2) := by
  have hx : 1 + x ^ 2 ≠ 0 := (realCoordinateInv_denominator_pos x).ne'
  unfold realCoordinateInv
  field_simp [hx]
  ring

theorem one_sub_realCoordinateInv (x : ℝ) :
    1 - realCoordinateInv x = (1 - x) ^ 2 / (1 + x ^ 2) := by
  have hx : 1 + x ^ 2 ≠ 0 := (realCoordinateInv_denominator_pos x).ne'
  unfold realCoordinateInv
  field_simp [hx]
  ring

theorem realCoordinateInv_kernel_numerator_pos (x : ℝ) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < 1 - 2 * x * s + x ^ 2 := by
  have hp : 0 < (1 - s) * (1 + s) :=
    mul_pos (sub_pos.mpr hs.2) (by linarith [hs.1])
  nlinarith [sq_nonneg (x - s)]

theorem realCoordinateInv_kernel_pos (x : ℝ) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < 1 - realCoordinateInv x * s := by
  rw [one_sub_realCoordinateInv_mul]
  exact div_pos (realCoordinateInv_kernel_numerator_pos x hs)
    (realCoordinateInv_denominator_pos x)

theorem one_sub_realCoordinateInv_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - realCoordinateInv x :=
  sub_pos.mpr (realCoordinateInv_mem hx).2

def realEnergyTau (e : ℝ) : ℝ := 1 - e
def realEnergyRho (e x : ℝ) : ℝ := 1 - e * (1 - x)
def realEnergySigma (e s : ℝ) : ℝ := 1 - e * Real.sqrt (1 - s)

theorem realEnergyTau_bounds {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) :
    0 < realEnergyTau e ∧ realEnergyTau e < 1 := by
  unfold realEnergyTau
  constructor <;> linarith [he.1, he.2]

theorem realEnergyRho_bounds {e x : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    1 - 2 * e < realEnergyRho e x ∧ realEnergyRho e x < 1 := by
  unfold realEnergyRho
  have h1 := mul_pos he.1 (sub_pos.mpr hx.2)
  have h2 := mul_pos he.1 (show 0 < x + 1 by linarith [hx.1])
  constructor <;> nlinarith

theorem realEnergyRho_mem {e x : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) : realEnergyRho e x ∈ Ioo (0 : ℝ) 1 := by
  have hb := realEnergyRho_bounds he hx
  exact ⟨by linarith [hb.1, he.2], hb.2⟩

theorem realEnergySigma_bounds {e s : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    1 - e < realEnergySigma e s ∧ realEnergySigma e s < 1 := by
  have hs0 : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.mpr (sub_pos.mpr hs.2)
  have hs1 : Real.sqrt (1 - s) < 1 := by
    have ht := Real.sqrt_lt_sqrt (sub_pos.mpr hs.2).le (show 1 - s < 1 by linarith [hs.1])
    simpa only [Real.sqrt_one] using ht
  unfold realEnergySigma
  have h1 := mul_pos he.1 hs0
  have h2 := mul_pos he.1 (sub_pos.mpr hs1)
  constructor <;> nlinarith

theorem realEnergySigma_mem {e s : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : s ∈ Ioo (0 : ℝ) 1) : realEnergySigma e s ∈ Ioo (0 : ℝ) 1 := by
  have hb := realEnergySigma_bounds he hs
  exact ⟨by linarith [hb.1, he.2], hb.2⟩

theorem realEnergyRho_mul_bounds {e x y : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    0 < realEnergyRho e x * realEnergyRho e y ∧
      realEnergyRho e x * realEnergyRho e y < 1 ∧
      1 - realEnergyRho e x * realEnergyRho e y ≤ 4 * e := by
  have hxm := realEnergyRho_mem he hx
  have hym := realEnergyRho_mem he hy
  have hxb := (realEnergyRho_bounds he hx).1
  have hyb := (realEnergyRho_bounds he hy).1
  refine ⟨mul_pos hxm.1 hym.1, ?_, ?_⟩
  · have hm := mul_lt_mul_of_pos_left hym.2 hxm.1
    nlinarith [hxm.2]
  · have he0 : 0 < 1 - 2 * e := by linarith [he.2]
    have hp := mul_le_mul hxb.le hyb.le he0.le hxm.1.le
    nlinarith [sq_nonneg e]

theorem realEnergySigma_mul_bounds {e s t : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 - e) ^ 2 ≤ realEnergySigma e s * realEnergySigma e t ∧
      realEnergySigma e s * realEnergySigma e t < 1 := by
  have hsm := realEnergySigma_mem he hs
  have htm := realEnergySigma_mem he ht
  have hsb := (realEnergySigma_bounds he hs).1
  have htb := (realEnergySigma_bounds he ht).1
  have he0 : 0 < 1 - e := by linarith [he.2]
  constructor
  · have hp := mul_le_mul hsb.le htb.le he0.le hsm.1.le
    nlinarith
  · have hp := mul_lt_mul_of_pos_left htm.2 hsm.1
    nlinarith [hsm.2]

end

open Set
open scoped BigOperators

theorem prod_pair_factors {m : ℕ} (w : Fin m → ℝ) :
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (w i * w j)) =
      ∏ i : Fin m, w i ^ (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
    simp only [Fin.prod_Ioi_succ]
    rw [ih, Fin.prod_univ_succ]
    simp only [Nat.add_sub_cancel, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_fin]
    by_cases hm : m = 0
    · subst m
      simp
    · have hp (i : Fin m) : w i.succ * w i.succ ^ (m - 1) = w i.succ ^ m := by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp_rw [hp]

theorem prod_pair_const (m : ℕ) (c : ℝ) :
    (∏ i : Fin m, ∏ _j ∈ Finset.Ioi i, c) = c ^ (m.choose 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
    simp only [Fin.prod_Ioi_succ]
    rw [ih]
    simp only [Finset.prod_const, Finset.card_fin]
    have hc : (m + 1).choose 2 = m + m.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ m 1
    rw [hc, pow_add]

private theorem abs_inv_sub_inv_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    |a⁻¹ - b⁻¹| = |a - b| / (|a| * |b|) := by
  have heq : a⁻¹ - b⁻¹ = -(a - b) / (a * b) := by
    field_simp [ha, hb]
    ring
  rw [heq, abs_div, abs_neg, abs_mul]

theorem abs_vandermonde_inv {m : ℕ} (x : Fin m → ℝ) (hx0 : ∀ i, x i ≠ 0) :
    |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| =
      |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)| /
        (∏ i : Fin m, |x i| ^ (m - 1)) := by
  have hp (i j : Fin m) : |(x j)⁻¹ - (x i)⁻¹| =
      |x j - x i| / (|x i| * |x j|) := by
    rw [abs_inv_sub_inv_eq (hx0 j) (hx0 i), mul_comm |x j| |x i|]
  simp_rw [Finset.abs_prod, hp, Finset.prod_div_distrib]
  rw [prod_pair_factors]

theorem prod_realCoordinateInv_kernel {m : ℕ} (x s : Fin m → ℝ) :
    (∏ i : Fin m, ∏ j : Fin m, (1 - realCoordinateInv (x i) * s j)) =
      (∏ i : Fin m, ∏ j : Fin m, (1 - 2 * x i * s j + x i ^ 2)) /
        (∏ i : Fin m, (1 + x i ^ 2) ^ m) := by
  simp_rw [one_sub_realCoordinateInv_mul, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem abs_vandermonde_realCoordinateInv {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    |∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
      (realCoordinateInv (x j) - realCoordinateInv (x i))| =
      (2 : ℝ) ^ (m.choose 2) *
        |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)| *
        (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) /
        (∏ i : Fin m, (1 + x i ^ 2) ^ (m - 1)) := by
  have hp (i j : Fin m) :
      |realCoordinateInv (x j) - realCoordinateInv (x i)| =
        2 * |x j - x i| * (1 - x i * x j) /
          ((1 + x i ^ 2) * (1 + x j ^ 2)) := by
    simpa only [mul_comm (x j) (x i), mul_comm (1 + x j ^ 2) (1 + x i ^ 2)] using
      abs_realCoordinateInv_sub (hx j) (hx i)
  simp_rw [Finset.abs_prod, hp, Finset.prod_div_distrib]
  rw [prod_pair_factors]
  simp only [Finset.prod_mul_distrib]
  rw [prod_pair_const]

end

open Set

theorem energy_cross_relative_size {x s : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    |x| * ((1 - x) + Real.sqrt (1 - s)) ≤
      3 * Real.sqrt (1 - 2 * x * s + x ^ 2) := by
  let b := Real.sqrt (1 - s)
  let q := Real.sqrt (1 - 2 * x * s + x ^ 2)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = 1 - s := Real.sq_sqrt (sub_pos.mpr hs.2).le
  have hq2 : q ^ 2 = 1 - 2 * x * s + x ^ 2 :=
    Real.sq_sqrt (realCoordinateInv_kernel_numerator_pos x hs).le
  have hb1 : b ≤ 1 := by
    dsimp only [b]
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show 1 - s ≤ 1 by linarith [hs.1])
  change |x| * ((1 - x) + b) ≤ 3 * q
  by_cases hx0 : 0 ≤ x
  · have ha0 : 0 ≤ 1 - x := (sub_pos.mpr hx.2).le
    have hdecomp : q ^ 2 = (1 - x) ^ 2 + 2 * x * b ^ 2 := by
      rw [hq2, hb2]
      ring
    have haq : 1 - x ≤ q := by
      apply (sq_le_sq₀ ha0 hq0).mp
      rw [hdecomp]
      nlinarith [mul_nonneg hx0 (sq_nonneg b)]
    have hxc : 0 ≤ 2 * x - x ^ 2 := by
      nlinarith [mul_nonneg hx0 ha0]
    have hxb : x * b ≤ q := by
      apply (sq_le_sq₀ (mul_nonneg hx0 hb0) hq0).mp
      rw [hdecomp]
      nlinarith [mul_nonneg hxc (sq_nonneg b), sq_nonneg (1 - x)]
    have hxa : x * (1 - x) ≤ q := by
      calc
        _ ≤ 1 * (1 - x) := mul_le_mul_of_nonneg_right hx.2.le ha0
        _ ≤ q := by simpa only [one_mul] using haq
    rw [abs_of_nonneg hx0]
    nlinarith
  · have hxneg : x ≤ 0 := le_of_not_ge hx0
    have hq1 : 1 ≤ q := by
      apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hq0).mp
      rw [hq2]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hxneg hs.1.le, sq_nonneg x]
    have hab : 0 ≤ (1 - x) + b := by linarith [hx.2]
    calc
      _ ≤ 1 * ((1 - x) + b) :=
        mul_le_mul_of_nonneg_right (abs_lt.mpr hx).le hab
      _ ≤ 3 := by linarith [hx.1]
      _ ≤ 3 * q := by linarith

theorem realEnergy_cross_node_error {e x s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    |x - realEnergyRho e x * realEnergySigma e s * x| ≤
      3 * e * Real.sqrt (1 - 2 * x * s + x ^ 2) := by
  let d := realEnergyRho e x * realEnergySigma e s
  let b := Real.sqrt (1 - s)
  have hr := realEnergyRho_mem he hx
  have ht := realEnergySigma_mem he hs
  have hd1 : d ≤ 1 := by
    calc
      d ≤ realEnergyRho e x * 1 := mul_le_mul_of_nonneg_left ht.2.le hr.1.le
      _ ≤ 1 := by simpa only [mul_one] using hr.2.le
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have herr : 1 - d ≤ e * ((1 - x) + b) := by
    calc
      1 - d = e * ((1 - x) + b) - (e * (1 - x)) * (e * b) := by
        dsimp only [d, b, realEnergyRho, realEnergySigma]
        ring
      _ ≤ e * ((1 - x) + b) :=
        sub_le_self _ (mul_nonneg
          (mul_nonneg he.1.le (sub_pos.mpr hx.2).le) (mul_nonneg he.1.le hb0))
  have hsize := energy_cross_relative_size hx hs
  change |x| * ((1 - x) + b) ≤ 3 * Real.sqrt (1 - 2 * x * s + x ^ 2) at hsize
  change |x - d * x| ≤ 3 * e * Real.sqrt (1 - 2 * x * s + x ^ 2)
  calc
    _ = (1 - d) * |x| := by
      rw [show x - d * x = (1 - d) * x by ring, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr hd1)]
    _ ≤ (e * ((1 - x) + b)) * |x| := mul_le_mul_of_nonneg_right herr (abs_nonneg x)
    _ = e * (|x| * ((1 - x) + b)) := by ring
    _ ≤ e * (3 * Real.sqrt (1 - 2 * x * s + x ^ 2)) :=
      mul_le_mul_of_nonneg_left hsize he.1.le
    _ = _ := by ring

theorem realEnergy_cross_quadratic_le {e x s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    1 - 2 * (realEnergyRho e x * realEnergySigma e s * x) * s +
        (realEnergyRho e x * realEnergySigma e s * x) ^ 2 ≤
      (1 + 3 * e) ^ 2 * (1 - 2 * x * s + x ^ 2) := by
  let u := realEnergyRho e x * realEnergySigma e s * x
  let δ := x - u
  let q := Real.sqrt (1 - 2 * x * s + x ^ 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 1 - 2 * x * s + x ^ 2 :=
    Real.sq_sqrt (realCoordinateInv_kernel_numerator_pos x hs).le
  have hδ : |δ| ≤ 3 * e * q := realEnergy_cross_node_error he hx hs
  have hr0 : 0 ≤ 3 * e * q :=
    mul_nonneg (mul_nonneg (by norm_num) he.1.le) hq0
  have hsx : |s - x| ≤ q := by
    apply (sq_le_sq₀ (abs_nonneg _) hq0).mp
    rw [sq_abs, hq2]
    have hp : 0 < (1 - s) * (1 + s) :=
      mul_pos (sub_pos.mpr hs.2) (by linarith [hs.1])
    nlinarith
  have hδ2 : δ ^ 2 ≤ (3 * e * q) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg δ) hr0).mpr hδ
  have hcross : δ * (s - x) ≤ (3 * e * q) * q := by
    calc
      _ ≤ |δ * (s - x)| := le_abs_self _
      _ = |δ| * |s - x| := abs_mul _ _
      _ ≤ (3 * e * q) * q := mul_le_mul hδ hsx (abs_nonneg _) hr0
  change 1 - 2 * u * s + u ^ 2 ≤ (1 + 3 * e) ^ 2 * (1 - 2 * x * s + x ^ 2)
  calc
    _ = (1 - 2 * x * s + x ^ 2) + 2 * δ * (s - x) + δ ^ 2 := by
      dsimp only [δ]
      ring
    _ ≤ (1 - 2 * x * s + x ^ 2) + 2 * ((3 * e * q) * q) + (3 * e * q) ^ 2 := by
      nlinarith only [hcross, hδ2]
    _ = _ := by
      rw [← hq2]
      ring

theorem realEnergy_cross_kernel_le {e x s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    -Real.log (1 - 2 * x * s + x ^ 2) ≤
      -Real.log (1 - 2 * (realEnergyRho e x * realEnergySigma e s * x) * s +
        (realEnergyRho e x * realEnergySigma e s * x) ^ 2) + 6 * e := by
  have hQ := realCoordinateInv_kernel_numerator_pos x hs
  have hD := realCoordinateInv_kernel_numerator_pos
    (realEnergyRho e x * realEnergySigma e s * x) hs
  have hfac : 0 < 1 + 3 * e := by linarith [he.1]
  have hlog := Real.log_le_log hD (realEnergy_cross_quadratic_le he hx hs)
  rw [Real.log_mul (pow_ne_zero 2 hfac.ne') hQ.ne', Real.log_pow] at hlog
  simp only [Nat.cast_ofNat] at hlog
  have hcost := Real.log_le_sub_one_of_pos hfac
  linarith only [hlog, hcost]

theorem energy_log_opposite_sign {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.log (1 + q) - Real.log (1 + r * q) ≤ 1 - r := by
  have hx : 0 < 1 + q := by linarith
  have hy : 0 < 1 + r * q := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at hl
  have he : (1 + q) / (1 + r * q) - 1 = (1 - r) * q / (1 + r * q) := by
    field_simp [hy.ne']
    ring
  rw [he] at hl
  calc
    _ ≤ (1 - r) * q / (1 + r * q) := hl
    _ ≤ 1 - r := by
      apply (div_le_iff₀ hy).mpr
      have hq := mul_le_mul_of_nonneg_left hq1 (sub_nonneg.mpr hr1)
      have hd := mul_le_mul_of_nonneg_left
        (show 1 ≤ 1 + r * q by nlinarith [mul_nonneg hr0 hq0]) (sub_nonneg.mpr hr1)
      nlinarith


theorem realEnergy_power_kernel_le {e x y : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    Real.log (1 - x * y) ≤
      Real.log (1 - (realEnergyRho e x * realEnergyRho e y) * (x * y)) + 4 * e := by
  let r := realEnergyRho e x * realEnergyRho e y
  have hr := realEnergyRho_mul_bounds he hx hy
  have hr0 : 0 ≤ r := hr.1.le
  have hr1 : r ≤ 1 := hr.2.1.le
  have hrerr : 1 - r ≤ 4 * e := hr.2.2
  have hu : |x * y| < 1 := by
    rw [abs_mul]
    calc
      |x| * |y| ≤ |x| * 1 :=
        mul_le_mul_of_nonneg_left (abs_lt.mpr hy).le (abs_nonneg x)
      _ = |x| := mul_one _
      _ < 1 := abs_lt.mpr hx
  change Real.log (1 - x * y) ≤ Real.log (1 - r * (x * y)) + 4 * e
  by_cases hxy : 0 ≤ x * y
  · have hm := mul_le_mul_of_nonneg_right hr1 hxy
    have hl := Real.log_le_log (energy_one_sub_mul_pos hx hy)
      (show 1 - x * y ≤ 1 - r * (x * y) by nlinarith)
    linarith [he.1]
  · have hq0 : 0 ≤ -(x * y) := by linarith
    have hq1 : -(x * y) ≤ 1 := by linarith [(abs_lt.mp hu).1]
    have hl := energy_log_opposite_sign hq0 hq1 hr0 hr1
    have heq : 1 + r * -(x * y) = 1 - r * (x * y) := by ring
    rw [heq] at hl
    change Real.log (1 - x * y) - Real.log (1 - r * (x * y)) ≤ 1 - r at hl
    linarith

open Set

theorem realEnergy_power_diagonal_nonneg_side {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : 0 ≤ x) :
    1 - x ≤ 1 - realEnergyRho e x ^ 2 * x ^ 2 := by
  have hr := realEnergyRho_mem he hx
  have hr2 : realEnergyRho e x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hr.1.le (sub_nonneg.mpr hr.2.le)]
  have hp := mul_le_mul_of_nonneg_right hr2 (sq_nonneg x)
  have hxx := mul_nonneg hx0 (sub_nonneg.mpr hx.2.le)
  nlinarith

theorem realEnergy_power_diagonal_nonpos_side {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≤ 0) :
    e ≤ 1 - realEnergyRho e x ^ 2 * x ^ 2 := by
  have hr := realEnergyRho_mem he hx
  have he0 : 0 ≤ 1 - e := by linarith [he.2]
  have hrle : realEnergyRho e x ≤ 1 - e := by
    unfold realEnergyRho
    nlinarith [mul_nonpos_of_nonneg_of_nonpos he.1.le hx0]
  have hr2 : realEnergyRho e x ^ 2 ≤ (1 - e) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrle) (add_nonneg he0 hr.1.le)]
  have hxx : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - x by linarith [hx.2])
      (show 0 ≤ 1 + x by linarith [hx.1])]
  have hp := mul_le_mul_of_nonneg_left hxx (sq_nonneg (realEnergyRho e x))
  have hee := mul_nonneg he.1.le he0
  nlinarith

theorem realEnergy_log_power_diagonal_ge {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.log (1 - x) + Real.log e - Real.log 2 ≤
      Real.log (1 - realEnergyRho e x ^ 2 * x ^ 2) := by
  by_cases hx0 : 0 ≤ x
  · have hl := Real.log_le_log (sub_pos.mpr hx.2)
      (realEnergy_power_diagonal_nonneg_side he hx hx0)
    have he2 := Real.log_le_log he.1 (show e ≤ 2 by linarith [he.2])
    linarith
  · have hl := Real.log_le_log he.1
      (realEnergy_power_diagonal_nonpos_side he hx (le_of_not_ge hx0))
    have hx2 := Real.log_le_log (sub_pos.mpr hx.2)
      (show 1 - x ≤ 2 by linarith [hx.1])
    linarith

theorem realEnergy_sigma_diagonal_ge {e s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    e * Real.sqrt (1 - s) ≤ 1 - realEnergySigma e s ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (1 - s) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [hs.1])
  have ht0 : 0 ≤ e * Real.sqrt (1 - s) := mul_nonneg he.1.le hs0
  have ht1 : e * Real.sqrt (1 - s) ≤ 1 := by
    have hp := mul_le_mul_of_nonneg_left hs1 he.1.le
    nlinarith [he.2]
  have hp := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  unfold realEnergySigma
  nlinarith

theorem realEnergy_log_sigma_diagonal_ge {e s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    Real.log e + Real.log (1 - s) / 2 ≤ Real.log (1 - realEnergySigma e s ^ 2) := by
  have hs0 : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.mpr (sub_pos.mpr hs.2)
  have hl := Real.log_le_log (mul_pos he.1 hs0) (realEnergy_sigma_diagonal_ge he hs)
  rw [Real.log_mul he.1.ne' hs0.ne', Real.log_sqrt (sub_pos.mpr hs.2).le] at hl
  exact hl

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.MixedPolynomial
namespace OAI

noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem mixedPolynomial_kernel_eq (P Q : ℝ[X]) (t s : ℝ) :
    (|t| / Real.sqrt (1 - t ^ 2)) * (P.eval t * Q.eval s) / (1 - t * s) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) *
          ((|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)) := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [Polynomial.sum_def, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem integrable_mixedPolynomial (P Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ => (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
      (P.eval p.1 * Q.eval p.2) / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  simp_rw [mixedPolynomial_kernel_eq]
  exact integrable_finsetSum P.support fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_mixedKernel i j).const_mul (P.coeff i * Q.coeff j)

theorem integral_prod_mixedPolynomial (P Q : ℝ[X]) :
    (∫ p : ℝ × ℝ, (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
      (P.eval p.1 * Q.eval p.2) / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * mixedMoment (X ^ i) (X ^ j) := by
  simp_rw [mixedPolynomial_kernel_eq]
  rw [integral_finsetSum P.support (fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_mixedKernel i j).const_mul (P.coeff i * Q.coeff j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Q.support (fun j _ =>
    (integrable_mixedKernel i j).const_mul (P.coeff i * Q.coeff j))]
  simp only [MeasureTheory.integral_const_mul, mixedMoment_X_pow_eq_integral_prod]

theorem mixedMoment_eq_sum (P Q : ℝ[X]) :
    mixedMoment P Q = ∑ i ∈ P.support, ∑ j ∈ Q.support,
      (P.coeff i * Q.coeff j) * mixedMoment (X ^ i) (X ^ j) := by
  have h := integral_prod
    (fun p : ℝ × ℝ => (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
      (P.eval p.1 * Q.eval p.2) / (1 - p.1 * p.2))
    (integrable_mixedPolynomial P Q)
  rw [integral_prod_mixedPolynomial] at h
  simpa only [mixedMoment,
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h.symm

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.ZetaPolynomial
namespace OAI

noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem zetaPolynomial_kernel_eq (P Q : ℝ[X]) (t s : ℝ) :
    P.eval t * Q.eval s / (1 - t * s) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * (t ^ i * s ^ j / (1 - t * s)) := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [Polynomial.sum_def, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem integrable_zetaPolynomial (P Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ => P.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  simp_rw [zetaPolynomial_kernel_eq]
  exact integrable_finsetSum P.support fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_zetaKernel i j).const_mul (P.coeff i * Q.coeff j)

theorem integral_prod_zetaPolynomial (P Q : ℝ[X]) :
    (∫ p : ℝ × ℝ, P.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * zetaSeries i j := by
  simp_rw [zetaPolynomial_kernel_eq]
  rw [integral_finsetSum P.support (fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_zetaKernel i j).const_mul (P.coeff i * Q.coeff j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Q.support (fun j _ =>
    (integrable_zetaKernel i j).const_mul (P.coeff i * Q.coeff j))]
  simp only [MeasureTheory.integral_const_mul, integral_prod_zetaKernel]

theorem zetaMoment_eq_sum (P Q : ℝ[X]) :
    zetaMoment P Q = ∑ i ∈ P.support, ∑ j ∈ Q.support,
      (P.coeff i * Q.coeff j) * zetaSeries i j := by
  have h := integral_prod
    (fun p : ℝ × ℝ => P.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2))
    (integrable_zetaPolynomial P Q)
  rw [integral_prod_zetaPolynomial] at h
  simpa only [zetaMoment,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h.symm



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.RealPairedIntegral
namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set

def realPlaceMeasure : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
    (fun t => ENNReal.ofReal (|t| / Real.sqrt (1 - t ^ 2)))

private theorem realPlaceWeight_nonneg (t : ℝ) :
    0 ≤ |t| / Real.sqrt (1 - t ^ 2) :=
  div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

private theorem measurable_realPlaceDensity :
    Measurable (fun t : ℝ => ENNReal.ofReal (|t| / Real.sqrt (1 - t ^ 2))) := by
  fun_prop

theorem integrable_realPlaceMeasure_iff (f : ℝ → ℝ) :
    Integrable f realPlaceMeasure ↔
      Integrable (fun t => (|t| / Real.sqrt (1 - t ^ 2)) * f t)
        (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  simpa only [realPlaceMeasure, ENNReal.toReal_ofReal (realPlaceWeight_nonneg _),
    smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' measurable_realPlaceDensity
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g := f))

theorem integral_realPlaceMeasure (f : ℝ → ℝ) :
    (∫ t, f t ∂realPlaceMeasure) =
      ∫ t in Ioo (-1 : ℝ) 1, (|t| / Real.sqrt (1 - t ^ 2)) * f t := by
  simpa only [realPlaceMeasure, ENNReal.toReal_ofReal (realPlaceWeight_nonneg _),
    smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul measurable_realPlaceDensity
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f)

theorem realPlaceMeasure_univ : realPlaceMeasure univ = 2 := by
  have hi : Integrable (fun t : ℝ => |t| / Real.sqrt (1 - t ^ 2))
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (show (-1 : ℝ) ≤ 1 by norm_num)).mp (intervalIntegrable_scalarMoment 0)
    change Integrable (fun t : ℝ => t ^ 0 * (|t| / Real.sqrt (1 - t ^ 2)))
      (volume.restrict (Ioo (-1 : ℝ) 1)) at h
    simpa only [pow_zero, one_mul] using h
  have hv : (∫ t in Ioo (-1 : ℝ) 1, |t| / Real.sqrt (1 - t ^ 2)) = 2 := by
    simpa only [scalarMoment, pow_zero, one_mul,
      intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
      integral_Ioc_eq_integral_Ioo] using scalarMoment_zero
  rw [realPlaceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall realPlaceWeight_nonneg), hv]
  norm_num

instance : IsFiniteMeasure realPlaceMeasure where
  measure_univ_lt_top := by rw [realPlaceMeasure_univ]; norm_num

theorem integrable_realPlaceMeasure_prod_iff (f : ℝ × ℝ → ℝ) :
    Integrable f (realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) ↔
      Integrable (fun p => (|p.1| / Real.sqrt (1 - p.1 ^ 2)) * f p)
        ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1))) := by
  unfold realPlaceMeasure
  rw [prod_withDensity_left measurable_realPlaceDensity]
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (|p.1| / Real.sqrt (1 - p.1 ^ 2))) :=
    measurable_realPlaceDensity.comp measurable_fst
  simpa only [ENNReal.toReal_ofReal (realPlaceWeight_nonneg _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' hm
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g := f))

theorem integral_realPlaceMeasure_prod (f : ℝ × ℝ → ℝ) :
    (∫ p, f p ∂realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ p, (|p.1| / Real.sqrt (1 - p.1 ^ 2)) * f p
        ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
  unfold realPlaceMeasure
  rw [prod_withDensity_left measurable_realPlaceDensity]
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (|p.1| / Real.sqrt (1 - p.1 ^ 2))) :=
    measurable_realPlaceDensity.comp measurable_fst
  simpa only [ENNReal.toReal_ofReal (realPlaceWeight_nonneg _), smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f)

section

open MeasureTheory Set Real

private theorem realCoordinateInv_deriv_nonneg {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2 := by
  have hp := mul_pos (sub_pos.mpr hx.2) (show (0 : ℝ) < 1 + x by linarith [hx.1])
  have hr : 0 < 1 - x ^ 2 := by nlinarith only [hp]
  exact div_nonneg (mul_nonneg (by norm_num) hr.le) (sq_nonneg _)

private theorem realCoordinate_weighted_comp (f : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ((|realCoordinateInv x| / sqrt (1 - realCoordinateInv x ^ 2)) *
      f (realCoordinateInv x)) * (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) =
        (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x) := by
  calc
    _ = ((|realCoordinateInv x| / sqrt (1 - realCoordinateInv x ^ 2)) *
      (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2)) * f (realCoordinateInv x) := by ring
    _ = _ := by rw [realCoordinate_weight_jacobian hx]

theorem integral_realPlaceMeasure_coordinate (f : ℝ → ℝ) :
    (∫ t, f t ∂realPlaceMeasure) =
      ∫ x in Ioo (-1 : ℝ) 1,
        (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x) := by
  let g : ℝ → ℝ := fun t => (|t| / sqrt (1 - t ^ 2)) * f t
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (-1 : ℝ)) (b := 1) (f := realCoordinateInv)
    (f' := fun x => 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) (g := g)
    continuous_realCoordinateInv.continuousOn (fun x _ => hasDerivAt_realCoordinateInv x)
    (by
      intro x hx
      apply realCoordinateInv_deriv_nonneg
      simpa only [min_eq_left (show (-1 : ℝ) ≤ 1 by norm_num),
        max_eq_right (show (-1 : ℝ) ≤ 1 by norm_num)] using hx)
  have he0 : realCoordinateInv (-1) = -1 := by norm_num [realCoordinateInv]
  have he1 : realCoordinateInv 1 = 1 := by norm_num [realCoordinateInv]
  rw [he0, he1] at hsub
  rw [integral_realPlaceMeasure]
  calc
    _ = ∫ t in (-1 : ℝ)..1, g t := by
      simp only [g, intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
        integral_Ioc_eq_integral_Ioo]
    _ = ∫ x in (-1 : ℝ)..1,
        g (realCoordinateInv x) * (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) := hsub.symm
    _ = ∫ x in (-1 : ℝ)..1,
        (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro x hx
      exact realCoordinate_weighted_comp f hx
    _ = _ := by
      rw [intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
        integral_Ioc_eq_integral_Ioo]

theorem integrable_realPlaceMeasure_coordinate_iff (f : ℝ → ℝ) :
    Integrable f realPlaceMeasure ↔
      Integrable (fun x : ℝ => (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x))
        (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  rw [integrable_realPlaceMeasure_iff]
  let g : ℝ → ℝ := fun t => (|t| / sqrt (1 - t ^ 2)) * f t
  have hsub := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (-1 : ℝ)) (b := 1) (f := realCoordinateInv)
    (f' := fun x => 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) (g := g)
    continuous_realCoordinateInv.continuousOn (fun x _ => hasDerivAt_realCoordinateInv x)
    (by
      intro x hx
      apply realCoordinateInv_deriv_nonneg
      simpa only [min_eq_left (show (-1 : ℝ) ≤ 1 by norm_num),
        max_eq_right (show (-1 : ℝ) ≤ 1 by norm_num)] using hx)
  have he0 : realCoordinateInv (-1) = -1 := by norm_num [realCoordinateInv]
  have he1 : realCoordinateInv 1 = 1 := by norm_num [realCoordinateInv]
  rw [he0, he1] at hsub
  have hcongr := intervalIntegrable_congr_uIoo (μ := volume)
    (f := fun x : ℝ => g (realCoordinateInv x) * (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2))
    (g := fun x : ℝ => (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x))
    (a := (-1 : ℝ)) (b := 1) (by
      intro x hx
      rw [uIoo_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] at hx
      exact realCoordinate_weighted_comp f hx)
  have hiff := hsub.symm.trans hcongr
  have hOld : IntervalIntegrable g volume (-1) 1 ↔
      Integrable g (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    intervalIntegrable_iff_integrableOn_Ioo_of_le (f := g)
      (show (-1 : ℝ) ≤ 1 by norm_num) (by finiteness) (by finiteness)
  have hNew :
      IntervalIntegrable (fun x : ℝ =>
        (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x)) volume (-1) 1 ↔
      Integrable (fun x : ℝ =>
        (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x))
          (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    intervalIntegrable_iff_integrableOn_Ioo_of_le
      (f := fun x : ℝ => (4 * |x| / (1 + x ^ 2) ^ 2) * f (realCoordinateInv x))
      (show (-1 : ℝ) ≤ 1 by norm_num) (by finiteness) (by finiteness)
  exact hOld.symm.trans (hiff.trans hNew)

end

open MeasureTheory Set Polynomial

private theorem restrict_mixed_rectangle_positive :
    (((volume.restrict (Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))).restrict
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) =
      (volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [← Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi (0 : ℝ) ∩ Ioo (-1 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨hx, _, h1⟩
      exact ⟨hx, h1⟩
    · rintro ⟨hx, h1⟩
      exact ⟨hx, by linarith, h1⟩
  rw [he]

theorem integrable_positive_zetaPolynomial (D Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ =>
      if 0 < p.1 then D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2) else 0)
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hfun : (fun p : ℝ × ℝ =>
      if 0 < p.1 then D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2) else 0) =
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator
        (fun p : ℝ × ℝ => D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2)) := by
    ext p
    simp only [indicator, mem_prod, mem_Ioi, mem_univ, and_true]
  rw [hfun, integrable_indicator_iff (measurableSet_Ioi.prod MeasurableSet.univ)]
  change Integrable _ _
  rw [restrict_mixed_rectangle_positive]
  exact integrable_zetaPolynomial D Q

theorem integral_positive_zetaPolynomial (D Q : ℝ[X]) :
    (∫ p : ℝ × ℝ,
      (if 0 < p.1 then D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2) else 0)
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) = zetaMoment D Q := by
  have hfun : (fun p : ℝ × ℝ =>
      if 0 < p.1 then D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2) else 0) =
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator
        (fun p : ℝ × ℝ => D.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2)) := by
    ext p
    simp only [indicator, mem_prod, mem_Ioi, mem_univ, and_true]
  rw [hfun, integral_indicator (measurableSet_Ioi.prod MeasurableSet.univ),
    restrict_mixed_rectangle_positive]
  exact (integral_prod_zetaPolynomial D Q).trans (zetaMoment_eq_sum D Q).symm

theorem integrable_realRowAmplitude (N r : ℕ) (Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ =>
      (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
        (realRowAmplitude N r p.1 * Q.eval p.2) / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hi := (integrable_mixedPolynomial (realPoly (rowP N r)) Q).sub
    ((integrable_positive_zetaPolynomial (realPoly (rowD N r)) Q).const_mul (3 / 2 : ℝ))
  apply hi.congr
  filter_upwards [ae_mem_mixed_rectangle] with p hp
  exact (realRowAmplitude_kernel_eq N r Q hp.1 p.2).symm

theorem integral_prod_realRowAmplitude (N r : ℕ) (Q : ℝ[X]) :
    (∫ p : ℝ × ℝ,
      (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
        (realRowAmplitude N r p.1 * Q.eval p.2) / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      mixedMoment (realPoly (rowP N r)) Q -
        (3 / 2 : ℝ) * zetaMoment (realPoly (rowD N r)) Q := by
  calc
    _ = ∫ p : ℝ × ℝ,
        ((|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
          ((realPoly (rowP N r)).eval p.1 * Q.eval p.2) / (1 - p.1 * p.2) -
          (3 / 2 : ℝ) * (if 0 < p.1 then
            (realPoly (rowD N r)).eval p.1 * Q.eval p.2 / (1 - p.1 * p.2) else 0))
        ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
      apply integral_congr_ae
      filter_upwards [ae_mem_mixed_rectangle] with p hp
      exact realRowAmplitude_kernel_eq N r Q hp.1 p.2
    _ = _ := by
      rw [integral_sub (integrable_mixedPolynomial (realPoly (rowP N r)) Q)
        ((integrable_positive_zetaPolynomial (realPoly (rowD N r)) Q).const_mul (3 / 2 : ℝ)),
        integral_const_mul, integral_positive_zetaPolynomial]
      rw [integral_prod_mixedPolynomial, ← mixedMoment_eq_sum]


theorem integrable_realPlaceRow (N r : ℕ) (Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ =>
      realRowAmplitude N r p.1 * Q.eval p.2 / (1 - p.1 * p.2))
      (realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  apply (integrable_realPlaceMeasure_prod_iff _).mpr
  simpa only [mul_div_assoc] using integrable_realRowAmplitude N r Q

theorem determinantEntry_eq_realPlace_product (N r k : ℕ) :
    determinantEntry N r k =
      ∫ p : ℝ × ℝ,
        realRowAmplitude N r p.1 * (filteredColumn N k).eval p.2 / (1 - p.1 * p.2)
        ∂realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [integral_realPlaceMeasure_prod]
  simpa only [determinantEntry, mul_div_assoc] using
    (integral_prod_realRowAmplitude N r (filteredColumn N k)).symm


open MeasureTheory Set Polynomial
open scoped BigOperators

theorem integrable_pairedDeterminant (N : ℕ) :
    Integrable (fun z : Fin (n N) → ℝ × ℝ =>
      Matrix.det (Matrix.of fun r k : Fin (n N) =>
        realRowAmplitude N r.val (z k).1 * (filteredColumn N k.val).eval (z k).2 /
          (1 - (z k).1 * (z k).2)))
      (Measure.pi (fun _ : Fin (n N) =>
        realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  classical
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  apply integrable_finsetSum
  intro σ _
  exact (Integrable.fintype_prod (fun k : Fin (n N) =>
    integrable_realPlaceRow N (σ k).val (filteredColumn N k.val))).const_mul _

theorem determinant_eq_paired_integral (N : ℕ) :
    determinant N =
      ∫ z : Fin (n N) → ℝ × ℝ,
        Matrix.det (Matrix.of fun r k : Fin (n N) =>
          realRowAmplitude N r.val (z k).1 * (filteredColumn N k.val).eval (z k).2 /
            (1 - (z k).1 * (z k).2))
        ∂Measure.pi (fun _ : Fin (n N) =>
          realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  classical
  let μ : Measure (ℝ × ℝ) :=
    realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))
  let F : Equiv.Perm (Fin (n N)) → (Fin (n N) → ℝ × ℝ) → ℝ := fun σ z =>
    ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∏ k : Fin (n N), realRowAmplitude N (σ k).val (z k).1 *
        (filteredColumn N k.val).eval (z k).2 / (1 - (z k).1 * (z k).2)
  have hF (σ : Equiv.Perm (Fin (n N))) :
      Integrable (F σ) (Measure.pi (fun _ : Fin (n N) => μ)) := by
    exact (Integrable.fintype_prod
      (μ := fun _ : Fin (n N) => μ)
      (f := fun k : Fin (n N) => fun p : ℝ × ℝ =>
        realRowAmplitude N (σ k).val p.1 * (filteredColumn N k.val).eval p.2 /
          (1 - p.1 * p.2))
      (fun k => integrable_realPlaceRow N (σ k).val (filteredColumn N k.val))).const_mul
        (((Equiv.Perm.sign σ : ℤ) : ℝ))
  have hsplit := integral_finsetSum (μ := Measure.pi (fun _ : Fin (n N) => μ))
    (f := F) Finset.univ (fun σ _ => hF σ)
  unfold determinant
  change (Matrix.of (fun r k : Fin (n N) => determinantEntry N r.val k.val)).det = _
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  change _ = ∫ z, ∑ σ : Equiv.Perm (Fin (n N)), F σ z
    ∂Measure.pi (fun _ : Fin (n N) => μ)
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro σ _
  dsimp only [F]
  rw [integral_const_mul, integral_fintype_prod_eq_prod
    (fun k : Fin (n N) => fun p : ℝ × ℝ =>
      realRowAmplitude N (σ k).val p.1 * (filteredColumn N k.val).eval p.2 /
        (1 - p.1 * p.2))]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact determinantEntry_eq_realPlace_product N (σ k).val k.val

theorem pairedDeterminant_factor (N : ℕ) (z : Fin (n N) → ℝ × ℝ) :
    Matrix.det (Matrix.of fun r k : Fin (n N) =>
      realRowAmplitude N r.val (z k).1 * (filteredColumn N k.val).eval (z k).2 /
        (1 - (z k).1 * (z k).2)) =
      Matrix.det (Matrix.of fun r k : Fin (n N) => realRowAmplitude N r.val (z k).1) *
        ∏ k : Fin (n N), (filteredColumn N k.val).eval (z k).2 /
          (1 - (z k).1 * (z k).2) := by
  have h := Matrix.det_mul_row
    (fun k : Fin (n N) => (filteredColumn N k.val).eval (z k).2 /
      (1 - (z k).1 * (z k).2))
    (Matrix.of fun r k : Fin (n N) => realRowAmplitude N r.val (z k).1)
  convert h using 1
  · congr 1
    funext r k
    simp only [Matrix.of_apply]
    ring
  · exact _root_.mul_comm _ _

theorem determinant_eq_paired_factored_integral (N : ℕ) :
    determinant N =
      ∫ z : Fin (n N) → ℝ × ℝ,
        Matrix.det (Matrix.of fun r k : Fin (n N) => realRowAmplitude N r.val (z k).1) *
          ∏ k : Fin (n N), (filteredColumn N k.val).eval (z k).2 /
            (1 - (z k).1 * (z k).2)
        ∂Measure.pi (fun _ : Fin (n N) =>
          realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  rw [determinant_eq_paired_integral]
  apply integral_congr_ae
  filter_upwards with z
  exact pairedDeterminant_factor N z

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealCauchyStep
namespace OAI

noncomputable section

open scoped BigOperators

namespace InternalCatalan

private theorem det_succ_schur {m : ℕ}
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (h00 : M 0 0 ≠ 0) :
    M.det = M 0 0 *
      Matrix.det (Matrix.of (fun i j : Fin m =>
        M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0)) := by
  classical
  let c : Fin (m + 1) → ℝ := fun i => if i = 0 then 0 else -(M i 0 / M 0 0)
  let E : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of (fun i j => M i j + c i * M 0 j)
  have hdet : E.det = M.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c 0
      (by simp only [c, if_pos rfl]) (fun _ _ => rfl)
  have hE00 : E 0 0 = M 0 0 := by simp [E, c]
  have hEi0 (i : Fin (m + 1)) (hi : i ≠ 0) : E i 0 = 0 := by
    simp only [E, Matrix.of_apply, c, if_neg hi]
    field_simp [h00]
    ring
  have htail : E.submatrix Fin.succ Fin.succ =
      Matrix.of (fun i j : Fin m =>
        M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0) := by
    ext i j
    simp only [Matrix.submatrix_apply, E, Matrix.of_apply, c,
      Fin.succ_ne_zero, ite_false]
    ring
  calc
    M.det = E.det := hdet.symm
    _ = _ := by
      rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
      · rw [Fin.val_zero, pow_zero, one_mul, hE00, Fin.succAbove_zero, htail]
      · intro i _ hi
        rw [hEi0 i hi, mul_zero, zero_mul]
      · simp

theorem cauchy_schur_entry (t0 ti s0 sj : ℝ)
    (h00 : 1 - t0 * s0 ≠ 0) (hi0 : 1 - ti * s0 ≠ 0)
    (h0j : 1 - t0 * sj ≠ 0) (hij : 1 - ti * sj ≠ 0) :
    (1 : ℝ) / (1 - ti * sj) -
        ((1 / (1 - ti * s0)) * (1 / (1 - t0 * sj))) / (1 / (1 - t0 * s0)) =
      ((ti - t0) / (1 - ti * s0)) *
        (((sj - s0) / (1 - t0 * sj)) * (1 / (1 - ti * sj))) := by
  have hi0' : 1 - s0 * ti ≠ 0 := by simpa only [mul_comm] using hi0
  have h0j' : 1 - sj * t0 ≠ 0 := by simpa only [mul_comm] using h0j
  apply mul_left_cancel₀ h00
  field_simp [hi0, hi0', h0j, h0j', hij]
  ring

theorem cauchy_det_succ {m : ℕ} (t s : Fin (m + 1) → ℝ)
    (hden : ∀ i j, 1 - t i * s j ≠ 0) :
    Matrix.det (Matrix.of (fun i j : Fin (m + 1) => (1 : ℝ) / (1 - t i * s j))) =
      (1 / (1 - t 0 * s 0)) *
        (∏ i : Fin m, (t i.succ - t 0) / (1 - t i.succ * s 0)) *
        (∏ j : Fin m, (s j.succ - s 0) / (1 - t 0 * s j.succ)) *
        Matrix.det (Matrix.of (fun i j : Fin m => (1 : ℝ) / (1 - t i.succ * s j.succ))) := by
  classical
  let C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of (fun i j => (1 : ℝ) / (1 - t i * s j))
  let T : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.of (fun i j => (1 : ℝ) / (1 - t i.succ * s j.succ))
  let rowFactor : Fin m → ℝ := fun i => (t i.succ - t 0) / (1 - t i.succ * s 0)
  let colFactor : Fin m → ℝ := fun j => (s j.succ - s 0) / (1 - t 0 * s j.succ)
  let B : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun i j => colFactor j * T i j)
  have hpivot : C 0 0 ≠ 0 := div_ne_zero one_ne_zero (hden 0 0)
  have htail :
      Matrix.of (fun i j : Fin m =>
        C i.succ j.succ - C i.succ 0 * C 0 j.succ / C 0 0) =
      Matrix.of (fun i j : Fin m => rowFactor i * B i j) := by
    ext i j
    simp only [C, T, B, rowFactor, colFactor, Matrix.of_apply]
    exact cauchy_schur_entry (t 0) (t i.succ) (s 0) (s j.succ)
      (hden 0 0) (hden i.succ 0) (hden 0 j.succ) (hden i.succ j.succ)
  have hB : B.det = (∏ j : Fin m, colFactor j) * T.det :=
    Matrix.det_mul_row colFactor T
  change C.det = C 0 0 * (∏ i : Fin m, rowFactor i) *
    (∏ j : Fin m, colFactor j) * T.det
  rw [det_succ_schur C hpivot, htail, Matrix.det_mul_column, hB]
  ring

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealPermutationAlgebra
namespace OAI

noncomputable section

open scoped BigOperators

namespace InternalCatalan

def rawRealIntegrand (N : ℕ) (t s : Fin (n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) *
    ∏ k : Fin (n N), (filteredColumn N k.val).eval (s k) / (1 - t k * s k)

def leftRealIntegrand (N : ℕ) (t s : Fin (n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) *
    Matrix.det (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s j))) *
      ∏ k : Fin (n N), (filteredColumn N k.val).eval (s k)

def doubleRealIntegrand (N : ℕ) (t s : Fin (n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) *
    Matrix.det (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s j))) *
      Matrix.det (Matrix.of (fun j k : Fin (n N) => (filteredColumn N k.val).eval (s j)))

theorem sum_rawRealIntegrand_permute_left (N : ℕ) (t s : Fin (n N) → ℝ) :
    (∑ σ : Equiv.Perm (Fin (n N)), rawRealIntegrand N (t ∘ σ) s) =
      leftRealIntegrand N t s := by
  classical
  unfold rawRealIntegrand leftRealIntegrand
  simp only [Function.comp_apply]
  rw [Matrix.det_apply'
    (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s j)))]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  have hA :
      Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t (σ i)))) =
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) :=
    Matrix.det_permute' σ
      (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i)))
  rw [hA]
  simp only [Matrix.of_apply, div_eq_mul_inv, one_mul, Finset.prod_mul_distrib]
  ring

theorem sum_leftRealIntegrand_permute_right (N : ℕ) (t s : Fin (n N) → ℝ) :
    (∑ τ : Equiv.Perm (Fin (n N)), leftRealIntegrand N t (s ∘ τ)) =
      doubleRealIntegrand N t s := by
  classical
  unfold leftRealIntegrand doubleRealIntegrand
  simp only [Function.comp_apply]
  rw [Matrix.det_apply'
    (Matrix.of (fun j k : Fin (n N) => (filteredColumn N k.val).eval (s j)))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  have hC :
      Matrix.det (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s (τ j)))) =
        ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          Matrix.det (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s j))) :=
    Matrix.det_permute' τ
      (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s j)))
  rw [hC]
  simp only [Matrix.of_apply]
  ring

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RealCauchyDeterminant
namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace InternalCatalan

private theorem vandermonde_prod_succ {m : ℕ} (t : Fin (m + 1) → ℝ) :
    (∏ i : Fin (m + 1), ∏ j ∈ Finset.Ioi i, (t j - t i)) =
      (∏ j : Fin m, (t j.succ - t 0)) *
        (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (t j.succ - t i.succ)) := by
  simp only [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ]

private theorem cauchy_denominator_prod_succ {m : ℕ} (t s : Fin (m + 1) → ℝ) :
    (∏ i : Fin (m + 1), ∏ j : Fin (m + 1), (1 - t i * s j)) =
      (1 - t 0 * s 0) * (∏ i : Fin m, (1 - t i.succ * s 0)) *
        (∏ j : Fin m, (1 - t 0 * s j.succ)) *
          (∏ i : Fin m, ∏ j : Fin m, (1 - t i.succ * s j.succ)) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.prod_univ_succ, Finset.prod_mul_distrib]
  ring

theorem cauchy_det_eq_prod {m : ℕ} (t s : Fin m → ℝ)
    (h : ∀ i j, 1 - t i * s j ≠ 0) :
    Matrix.det (Matrix.of (fun i j : Fin m => (1 : ℝ) / (1 - t i * s j))) =
      ((∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (t j - t i)) *
        (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (s j - s i))) /
          (∏ i : Fin m, ∏ j : Fin m, (1 - t i * s j)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [cauchy_det_succ t s h,
      ih (fun i => t i.succ) (fun j => s j.succ) (fun i j => h i.succ j.succ)]
    simp only [vandermonde_prod_succ, cauchy_denominator_prod_succ,
      Finset.prod_div_distrib]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem realCauchy_denominator_pos {m : ℕ} (t s : Fin m → ℝ)
    (ht : ∀ i, t i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (i j : Fin m) : 0 < 1 - t i * s j :=
  mixed_affine_denominator_pos (ht i) ⟨(hs j).1.le, (hs j).2.le⟩

theorem realCauchy_det_eq_prod {m : ℕ} (t s : Fin m → ℝ)
    (ht : ∀ i, t i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    Matrix.det (Matrix.of (fun i j : Fin m => (1 : ℝ) / (1 - t i * s j))) =
      ((∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (t j - t i)) *
        (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (s j - s i))) /
          (∏ i : Fin m, ∏ j : Fin m, (1 - t i * s j)) :=
  cauchy_det_eq_prod t s (fun i j => (realCauchy_denominator_pos t s ht hs i j).ne')

theorem doubleRealIntegrand_eq_products (N : ℕ) (t s : Fin (n N) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    doubleRealIntegrand N t s =
      Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) *
        (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (t j - t i)) *
        (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)) ^ 2 *
        (∏ j : Fin (n N), (s j) ^ b N * (1 - s j) ^ q N) /
        (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - t i * s j)) := by
  have hcolumn := filteredColumn_det_eq_prod N s
  change Matrix.det (Matrix.of (fun j k : Fin (n N) =>
    (filteredColumn N k.val).eval (s j))) = _ at hcolumn
  unfold doubleRealIntegrand
  rw [realCauchy_det_eq_prod t s ht hs, hcolumn]
  ring

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.RealFactoredIntegral
namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set
open scoped BigOperators

def realListPairMeasure (N : ℕ) :
    Measure ((Fin (n N) → ℝ) × (Fin (n N) → ℝ)) :=
  (Measure.pi (fun _ : Fin (n N) => realPlaceMeasure)).prod
    (Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))

private theorem list_permute_left_preserving (N : ℕ) (σ : Equiv.Perm (Fin (n N))) :
    MeasurePreserving
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin (n N) => ℝ) σ).symm.prodCongr
        (MeasurableEquiv.refl (Fin (n N) → ℝ)))
      (realListPairMeasure N) (realListPairMeasure N) := by
  exact (measurePreserving_piCongrLeft
    (fun _ : Fin (n N) => realPlaceMeasure) σ).symm.prod
      (MeasurePreserving.id _)

private theorem list_permute_right_preserving (N : ℕ) (σ : Equiv.Perm (Fin (n N))) :
    MeasurePreserving
      ((MeasurableEquiv.refl (Fin (n N) → ℝ)).prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (n N) => ℝ) σ).symm)
      (realListPairMeasure N) (realListPairMeasure N) := by
  exact (MeasurePreserving.id _).prod
    (measurePreserving_piCongrLeft
      (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)) σ).symm

private theorem integral_list_permute_left (N : ℕ) (σ : Equiv.Perm (Fin (n N)))
    (F : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) → ℝ) :
    (∫ p, F (p.1 ∘ σ, p.2) ∂realListPairMeasure N) =
      ∫ p, F p ∂realListPairMeasure N :=
  (list_permute_left_preserving N σ).integral_comp' F

private theorem integral_list_permute_right (N : ℕ) (σ : Equiv.Perm (Fin (n N)))
    (F : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) → ℝ) :
    (∫ p, F (p.1, p.2 ∘ σ) ∂realListPairMeasure N) =
      ∫ p, F p ∂realListPairMeasure N :=
  (list_permute_right_preserving N σ).integral_comp' F

private theorem integrable_list_permute_left (N : ℕ) (σ : Equiv.Perm (Fin (n N)))
    {F : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) → ℝ}
    (hF : Integrable F (realListPairMeasure N)) :
    Integrable (fun p => F (p.1 ∘ σ, p.2)) (realListPairMeasure N) :=
  (list_permute_left_preserving N σ).integrable_comp_of_integrable hF

private theorem integrable_list_permute_right (N : ℕ) (σ : Equiv.Perm (Fin (n N)))
    {F : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) → ℝ}
    (hF : Integrable F (realListPairMeasure N)) :
    Integrable (fun p => F (p.1, p.2 ∘ σ)) (realListPairMeasure N) :=
  (list_permute_right_preserving N σ).integrable_comp_of_integrable hF

theorem integrable_rawRealIntegrand (N : ℕ) :
    Integrable (fun p => rawRealIntegrand N p.1 p.2) (realListPairMeasure N) := by
  have hmap := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (n N))
    (fun _ => realPlaceMeasure) (fun _ => volume.restrict (Ioo (0 : ℝ) 1))
  apply (hmap.integrable_comp_emb
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (n N))).measurableEmbedding).mp
  apply (integrable_pairedDeterminant N).congr
  filter_upwards with z
  exact pairedDeterminant_factor N z

theorem determinant_eq_rawRealIntegrand (N : ℕ) :
    determinant N = ∫ p, rawRealIntegrand N p.1 p.2 ∂realListPairMeasure N := by
  have hmap := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (n N))
    (fun _ => realPlaceMeasure) (fun _ => volume.restrict (Ioo (0 : ℝ) 1))
  unfold realListPairMeasure
  rw [← hmap.integral_comp' (fun p => rawRealIntegrand N p.1 p.2)]
  exact determinant_eq_paired_factored_integral N

theorem integrable_leftRealIntegrand (N : ℕ) :
    Integrable (fun p => leftRealIntegrand N p.1 p.2) (realListPairMeasure N) := by
  classical
  have hi := integrable_finsetSum Finset.univ (fun (σ : Equiv.Perm (Fin (n N))) _ =>
    integrable_list_permute_left N σ (integrable_rawRealIntegrand N))
  apply hi.congr
  filter_upwards with p
  exact sum_rawRealIntegrand_permute_left N p.1 p.2

theorem integral_leftRealIntegrand (N : ℕ) :
    (∫ p, leftRealIntegrand N p.1 p.2 ∂realListPairMeasure N) =
      ((n N).factorial : ℝ) * determinant N := by
  classical
  calc
    _ = ∫ p, ∑ σ : Equiv.Perm (Fin (n N)),
        rawRealIntegrand N (p.1 ∘ σ) p.2 ∂realListPairMeasure N := by
      apply integral_congr_ae
      filter_upwards with p
      exact (sum_rawRealIntegrand_permute_left N p.1 p.2).symm
    _ = ∑ σ : Equiv.Perm (Fin (n N)),
        ∫ p, rawRealIntegrand N (p.1 ∘ σ) p.2 ∂realListPairMeasure N :=
      integral_finsetSum Finset.univ (fun (σ : Equiv.Perm (Fin (n N))) _ =>
        integrable_list_permute_left N σ (integrable_rawRealIntegrand N))
    _ = _ := by
      simp only [integral_list_permute_left N _ (fun p => rawRealIntegrand N p.1 p.2),
        ← determinant_eq_rawRealIntegrand, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem integrable_doubleRealIntegrand (N : ℕ) :
    Integrable (fun p => doubleRealIntegrand N p.1 p.2) (realListPairMeasure N) := by
  classical
  have hi := integrable_finsetSum Finset.univ (fun (σ : Equiv.Perm (Fin (n N))) _ =>
    integrable_list_permute_right N σ (integrable_leftRealIntegrand N))
  apply hi.congr
  filter_upwards with p
  exact sum_leftRealIntegrand_permute_right N p.1 p.2

theorem integral_doubleRealIntegrand (N : ℕ) :
    (∫ p, doubleRealIntegrand N p.1 p.2 ∂realListPairMeasure N) =
      ((n N).factorial : ℝ) ^ 2 * determinant N := by
  classical
  calc
    _ = ∫ p, ∑ σ : Equiv.Perm (Fin (n N)),
        leftRealIntegrand N p.1 (p.2 ∘ σ) ∂realListPairMeasure N := by
      apply integral_congr_ae
      filter_upwards with p
      exact (sum_leftRealIntegrand_permute_right N p.1 p.2).symm
    _ = ∑ σ : Equiv.Perm (Fin (n N)),
        ∫ p, leftRealIntegrand N p.1 (p.2 ∘ σ) ∂realListPairMeasure N :=
      integral_finsetSum Finset.univ (fun (σ : Equiv.Perm (Fin (n N))) _ =>
        integrable_list_permute_right N σ (integrable_leftRealIntegrand N))
    _ = _ := by
      simp only [integral_list_permute_right N _ (fun p => leftRealIntegrand N p.1 p.2),
        integral_leftRealIntegrand, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      ring


open MeasureTheory Set
open scoped BigOperators

theorem ae_realPlace_mem : ∀ᵐ t ∂realPlaceMeasure, t ∈ Ioo (-1 : ℝ) 1 := by
  unfold realPlaceMeasure
  apply (ae_withDensity_iff (by fun_prop)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact fun _ => ht

private theorem ae_realPlace_list_mem (N : ℕ) :
    ∀ᵐ t ∂Measure.pi (fun _ : Fin (n N) => realPlaceMeasure),
      ∀ i, t i ∈ Ioo (-1 : ℝ) 1 :=
  Filter.eventually_all.2 (fun _ => Measure.tendsto_eval_ae_ae.eventually ae_realPlace_mem)

private theorem ae_unit_list_mem (N : ℕ) :
    ∀ᵐ s ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)),
      ∀ j, s j ∈ Ioo (0 : ℝ) 1 :=
  Filter.eventually_all.2 (fun _ => Measure.tendsto_eval_ae_ae.eventually
    (ae_restrict_mem measurableSet_Ioo))

theorem ae_realList_rectangle (N : ℕ) :
    ∀ᵐ p ∂realListPairMeasure N,
      p ∈ (Set.univ.pi (fun _ : Fin (n N) => Ioo (-1 : ℝ) 1)) ×ˢ
        (Set.univ.pi (fun _ : Fin (n N) => Ioo (0 : ℝ) 1)) := by
  unfold realListPairMeasure
  apply (Measure.ae_prod_mem_iff_ae_ae_mem
    ((MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).prod
      (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)))).mpr
  filter_upwards [ae_realPlace_list_mem N] with t ht
  filter_upwards [ae_unit_list_mem N] with s hs
  exact ⟨fun i _ => ht i, fun j _ => hs j⟩

def productRealIntegrand (N : ℕ) (t s : Fin (n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) *
    (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (t j - t i)) *
    (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)) ^ 2 *
    (∏ j : Fin (n N), (s j) ^ b N * (1 - s j) ^ q N) /
    (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - t i * s j))

theorem doubleRealIntegrand_ae_eq_products (N : ℕ) :
    (fun p => doubleRealIntegrand N p.1 p.2) =ᵐ[realListPairMeasure N]
      (fun p => productRealIntegrand N p.1 p.2) := by
  filter_upwards [ae_realList_rectangle N] with p hp
  exact doubleRealIntegrand_eq_products N p.1 p.2
    (fun i => hp.1 i (Set.mem_univ i)) (fun j => hp.2 j (Set.mem_univ j))

theorem integrable_productRealIntegrand (N : ℕ) :
    Integrable (fun p => productRealIntegrand N p.1 p.2) (realListPairMeasure N) :=
  (integrable_doubleRealIntegrand N).congr (doubleRealIntegrand_ae_eq_products N)

theorem determinant_eq_productRealIntegral (N : ℕ) :
    determinant N = 1 / (((n N).factorial : ℝ) ^ 2) *
      ∫ t, (∫ s, productRealIntegrand N t s
        ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))
        ∂Measure.pi (fun _ : Fin (n N) => realPlaceMeasure) := by
  have hproduct : (∫ p, productRealIntegrand N p.1 p.2 ∂realListPairMeasure N) =
      ((n N).factorial : ℝ) ^ 2 * determinant N := by
    rw [← integral_congr_ae (doubleRealIntegrand_ae_eq_products N)]
    exact integral_doubleRealIntegrand N
  have h := integral_prod (fun p => productRealIntegrand N p.1 p.2)
    (integrable_productRealIntegrand N)
  change (∫ p, productRealIntegrand N p.1 p.2 ∂realListPairMeasure N) =
    (∫ t, (∫ s, productRealIntegrand N t s
      ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))
      ∂Measure.pi (fun _ : Fin (n N) => realPlaceMeasure)) at h
  rw [hproduct] at h
  rw [← h]
  have hn : ((n N).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n N)
  field_simp

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealCoordinateProduct
namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set

def realCoordinateMeasure : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal (4 * |x| / (1 + x ^ 2) ^ 2))

private theorem realCoordinateWeight_nonneg (x : ℝ) :
    0 ≤ 4 * |x| / (1 + x ^ 2) ^ 2 :=
  div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (sq_nonneg _)

private theorem measurable_realCoordinateDensity :
    Measurable (fun x : ℝ => ENNReal.ofReal (4 * |x| / (1 + x ^ 2) ^ 2)) := by
  fun_prop


theorem integral_realCoordinateMeasure (f : ℝ → ℝ) :
    (∫ x, f x ∂realCoordinateMeasure) =
      ∫ x in Ioo (-1 : ℝ) 1, (4 * |x| / (1 + x ^ 2) ^ 2) * f x := by
  simpa only [realCoordinateMeasure,
    ENNReal.toReal_ofReal (realCoordinateWeight_nonneg _), smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul measurable_realCoordinateDensity
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f)

theorem realCoordinateMeasure_univ : realCoordinateMeasure univ = 2 := by
  have hi : Integrable (fun x : ℝ => 4 * |x| / (1 + x ^ 2) ^ 2)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    simpa only [mul_one] using
      (integrable_realPlaceMeasure_coordinate_iff (fun _ => (1 : ℝ))).mp
        (integrable_const 1)
  have hv : (∫ x in Ioo (-1 : ℝ) 1, 4 * |x| / (1 + x ^ 2) ^ 2) = 2 := by
    have h := integral_realPlaceMeasure_coordinate (fun _ => (1 : ℝ))
    norm_num [integral_const, measureReal_def, realPlaceMeasure_univ] at h
    exact h.symm
  rw [realCoordinateMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall realCoordinateWeight_nonneg), hv]
  norm_num

instance : IsFiniteMeasure realCoordinateMeasure where
  measure_univ_lt_top := by rw [realCoordinateMeasure_univ]; norm_num

theorem integral_realPlace_eq_coordinate (f : ℝ → ℝ) :
    (∫ t, f t ∂realPlaceMeasure) =
      ∫ x, f (realCoordinateInv x) ∂realCoordinateMeasure := by
  rw [integral_realCoordinateMeasure, integral_realPlaceMeasure_coordinate]


theorem map_realCoordinateInv :
    Measure.map realCoordinateInv realCoordinateMeasure = realPlaceMeasure := by
  apply Measure.ext
  intro s hs
  have hr : (Measure.map realCoordinateInv realCoordinateMeasure).real s =
      realPlaceMeasure.real s := by
    rw [← integral_indicator_one hs, ← integral_indicator_one hs]
    exact (integral_map_of_stronglyMeasurable
      (μ := realCoordinateMeasure) (φ := realCoordinateInv)
      (f := s.indicator (1 : ℝ → ℝ))
      continuous_realCoordinateInv.measurable
      (stronglyMeasurable_const.indicator hs)).trans
        (integral_realPlace_eq_coordinate (s.indicator (1 : ℝ → ℝ))).symm
  have he := congrArg ENNReal.ofReal hr
  simpa only [measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)] using he

theorem measurePreserving_realCoordinateInv :
    MeasurePreserving realCoordinateInv realCoordinateMeasure realPlaceMeasure :=
  ⟨continuous_realCoordinateInv.measurable, map_realCoordinateInv⟩




theorem ae_realCoordinate_mem :
    ∀ᵐ x ∂realCoordinateMeasure, x ∈ Ioo (-1 : ℝ) 1 := by
  unfold realCoordinateMeasure
  apply (ae_withDensity_iff (by fun_prop)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact fun _ => hx

theorem ae_realCoordinate_ne_zero : ∀ᵐ x ∂realCoordinateMeasure, x ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  change realCoordinateMeasure ({0} : Set ℝ) = 0
  unfold realCoordinateMeasure
  exact measure_singleton _

theorem ae_realCoordinate_list_regular (N : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure),
      ∀ i, x i ∈ Ioo (-1 : ℝ) 1 ∧ x i ≠ 0 :=
  Filter.eventually_all.2 (fun i =>
    (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (n N) => realCoordinateMeasure) (i := i)).eventually
        (ae_realCoordinate_mem.and ae_realCoordinate_ne_zero))

open MeasureTheory Set

def realCoordinateListPairMeasure (N : ℕ) :
    Measure ((Fin (n N) → ℝ) × (Fin (n N) → ℝ)) :=
  (Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure)).prod
    (Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))

theorem measurePreserving_realCoordinate_list (N : ℕ) :
    MeasurePreserving (fun x : Fin (n N) → ℝ => fun i => realCoordinateInv (x i))
      (Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure))
      (Measure.pi (fun _ : Fin (n N) => realPlaceMeasure)) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_realCoordinateInv)

theorem measurePreserving_realCoordinate_pair (N : ℕ) :
    MeasurePreserving
      (fun p : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) =>
        ((fun i => realCoordinateInv (p.1 i)), p.2))
      (realCoordinateListPairMeasure N) (realListPairMeasure N) := by
  exact (measurePreserving_realCoordinate_list N).prod (MeasurePreserving.id _)

theorem integrable_coordinate_productRealIntegrand (N : ℕ) :
    Integrable (fun p =>
      productRealIntegrand N (fun i => realCoordinateInv (p.1 i)) p.2)
      (realCoordinateListPairMeasure N) :=
  (measurePreserving_realCoordinate_pair N).integrable_comp_of_integrable
    (integrable_productRealIntegrand N)

theorem integral_coordinate_productRealIntegrand (N : ℕ) :
    (∫ p, productRealIntegrand N (fun i => realCoordinateInv (p.1 i)) p.2
      ∂realCoordinateListPairMeasure N) =
      ∫ p, productRealIntegrand N p.1 p.2 ∂realListPairMeasure N := by
  have hm := measurePreserving_realCoordinate_pair N
  have hsm : AEStronglyMeasurable
      (fun p => productRealIntegrand N p.1 p.2)
      (Measure.map
        (fun p : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) =>
          ((fun i => realCoordinateInv (p.1 i)), p.2))
        (realCoordinateListPairMeasure N)) := by
    rw [hm.map_eq]
    exact (integrable_productRealIntegrand N).aestronglyMeasurable
  have he := (integral_map hm.aemeasurable hsm).symm
  rw [hm.map_eq] at he
  exact he

theorem determinant_eq_coordinateProductIntegral (N : ℕ) :
    determinant N = 1 / (((n N).factorial : ℝ) ^ 2) *
      ∫ x, (∫ s, productRealIntegrand N (fun i => realCoordinateInv (x i)) s
        ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))
        ∂Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure) := by
  rw [determinant_eq_productRealIntegral N]
  congr 1
  calc
    _ = ∫ p, productRealIntegrand N p.1 p.2 ∂realListPairMeasure N :=
      (integral_prod _ (integrable_productRealIntegrand N)).symm
    _ = ∫ p, productRealIntegrand N (fun i => realCoordinateInv (p.1 i)) p.2
        ∂realCoordinateListPairMeasure N :=
      (integral_coordinate_productRealIntegrand N).symm
    _ = _ := integral_prod _ (integrable_coordinate_productRealIntegrand N)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealHadamard
namespace OAI

noncomputable section

open scoped BigOperators InnerProductSpace

namespace InternalCatalan

theorem norm_det_le_of_entry_norm_eq {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : ∀ i j, ‖A i j‖ = w i) :
    ‖A.det‖ ≤ (Real.sqrt (m : ℝ)) ^ m * (∏ i, w i) := by
  classical
  let f : Fin m → EuclideanSpace ℂ (Fin m) :=
    fun i => WithLp.toLp 2 (A i)
  let e : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)) :=
    EuclideanSpace.basisFun (Fin m) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) =
      Fintype.card (Fin m) := finrank_euclideanSpace
  let b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  have hcoord : e.toBasis.toMatrix f = A.transpose := by
    ext i j
    change e.toBasis.repr (f j) i = A j i
    rw [OrthonormalBasis.coe_toBasis_repr_apply]
    rfl
  have hdet : e.toBasis.det f = A.det := by
    rw [Module.Basis.det_apply, hcoord, Matrix.det_transpose]
  have hchange : e.toBasis.det f =
      e.toBasis.det b * b.toBasis.det f := by
    simpa only [AlternatingMap.smul_apply, smul_eq_mul,
      OrthonormalBasis.coe_toBasis] using
      congrArg (fun D : AlternatingMap ℂ (EuclideanSpace ℂ (Fin m)) ℂ (Fin m) => D f)
        ((e.toBasis.det).eq_smul_basis_det b.toBasis)
  have hnormdet : ‖A.det‖ = ‖b.toBasis.det f‖ := by
    rw [← hdet, hchange, norm_mul,
      OrthonormalBasis.det_to_matrix_orthonormalBasis, one_mul]
  have htri : b.toBasis.det f = ∏ i, ⟪b i, f i⟫_ℂ :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hdim f
  have hrow (i : Fin m) : ‖f i‖ = Real.sqrt (m : ℝ) * w i := by
    rw [EuclideanSpace.norm_eq]
    simp only [f, hA, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq (hw i)]
  calc
    ‖A.det‖ = ∏ i, ‖⟪b i, f i⟫_ℂ‖ := by
      rw [hnormdet, htri, Complex.norm_prod]
    _ ≤ ∏ i, ‖f i‖ := by
      apply Finset.prod_le_prod
      · intro i _
        exact norm_nonneg _
      · intro i _
        simpa only [OrthonormalBasis.norm_eq_one, one_mul] using
          norm_inner_le_norm (𝕜 := ℂ) (b i) (f i)
    _ = (Real.sqrt (m : ℝ)) ^ m * (∏ i, w i) := by
      simp_rw [hrow]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealProjectiveVandermonde
namespace OAI

noncomputable section
open scoped BigOperators

namespace InternalCatalan

private theorem norm_real_add_I (z : ℝ) :
    ‖(z : ℂ) + Complex.I‖ = Real.sqrt (1 + z ^ 2) := by
  simp [Complex.norm_eq_sqrt_sq_add_sq, add_comm]

private theorem norm_real_sub_I (z : ℝ) :
    ‖(z : ℂ) - Complex.I‖ = Real.sqrt (1 + z ^ 2) := by
  simp [Complex.norm_eq_sqrt_sq_add_sq, add_comm]

theorem real_projectiveVandermonde_entry_norm {m : ℕ} (z : Fin m → ℝ)
    (i j : Fin m) :
    ‖Matrix.projVandermonde
      (fun i => (z i : ℂ) + Complex.I) (fun i => (z i : ℂ) - Complex.I) i j‖ =
      Real.sqrt (1 + z i ^ 2) ^ (m - 1) := by
  rw [Matrix.projVandermonde_apply, Complex.norm_mul, Complex.norm_pow, Complex.norm_pow,
    norm_real_add_I, norm_real_sub_I, ← pow_add]
  congr 1
  rw [Fin.val_rev]
  omega

private theorem real_projective_pair_norm (a b : ℝ) :
    ‖((b : ℂ) + Complex.I) * ((a : ℂ) - Complex.I) -
      ((a : ℂ) + Complex.I) * ((b : ℂ) - Complex.I)‖ = 2 * |b - a| := by
  have heq : ((b : ℂ) + Complex.I) * ((a : ℂ) - Complex.I) -
      ((a : ℂ) + Complex.I) * ((b : ℂ) - Complex.I) =
      (-2 * Complex.I) * ((b - a : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_mul, Complex.norm_mul, Complex.norm_real]
  norm_num [Real.norm_eq_abs]

private theorem prod_two_pairs (m : ℕ) :
    (∏ i : Fin m, ∏ _j ∈ Finset.Ioi i, (2 : ℝ)) = 2 ^ (m.choose 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
    simp only [Fin.prod_Ioi_succ]
    rw [ih]
    simp only [Finset.prod_const, Finset.card_fin]
    have hc : (m + 1).choose 2 = m + m.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ m 1
    rw [hc, pow_add]

theorem real_projectiveVandermonde_det_norm {m : ℕ} (z : Fin m → ℝ) :
    ‖Matrix.det (Matrix.projVandermonde
      (fun i => (z i : ℂ) + Complex.I) (fun i => (z i : ℂ) - Complex.I))‖ =
      2 ^ (m.choose 2) *
        |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (z j - z i)| := by
  rw [Matrix.det_projVandermonde]
  simp_rw [Complex.norm_prod, real_projective_pair_norm]
  simp only [Finset.prod_mul_distrib]
  rw [prod_two_pairs]
  simp_rw [Finset.abs_prod]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealWeightedVandermonde
namespace OAI

noncomputable section
open scoped BigOperators

namespace InternalCatalan

theorem weighted_real_vandermonde_le_sqrt {m : ℕ} (z : Fin m → ℝ) :
    |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (z j - z i)| ≤
      (Real.sqrt (m : ℝ)) ^ m / (2 : ℝ) ^ (m.choose 2) *
        (∏ i : Fin m, Real.sqrt (1 + z i ^ 2) ^ (m - 1)) := by
  have hh := norm_det_le_of_entry_norm_eq
    (Matrix.projVandermonde
      (fun i => (z i : ℂ) + Complex.I) (fun i => (z i : ℂ) - Complex.I))
    (fun i => Real.sqrt (1 + z i ^ 2) ^ (m - 1))
    (fun i => pow_nonneg (Real.sqrt_nonneg _) _)
    (real_projectiveVandermonde_entry_norm z)
  rw [real_projectiveVandermonde_det_norm] at hh
  have hd : 0 < (2 : ℝ) ^ (m.choose 2) := by positivity
  calc
    _ ≤ ((Real.sqrt (m : ℝ)) ^ m *
        (∏ i : Fin m, Real.sqrt (1 + z i ^ 2) ^ (m - 1))) /
          (2 : ℝ) ^ (m.choose 2) := by
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hh
    _ = _ := by ring



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.RealSheetIntegral
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial Set

theorem chebyshevT_eval_sheet (d : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (Chebyshev.T ℤ (d : ℤ)).eval₂ (Int.castRingHom ℝ) ((x + x⁻¹) / 2) =
      (x ^ d + (x⁻¹) ^ d) / 2 := by
  induction d using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp
  | more d ih0 ih1 =>
    have hi1 : (d : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) := by omega
    rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two]
    simp only [eval₂_sub, eval₂_mul, eval₂_ofNat, eval₂_X]
    rw [hi1, ih1, ih0]
    simp only [pow_add, pow_one, pow_two]
    linear_combination (x ^ d + (x⁻¹) ^ d) / 2 * (mul_inv_cancel₀ hx)

theorem chebyshevU_eval_sheet (d : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ((x⁻¹ - x) / 2) *
        (Chebyshev.U ℤ ((d : ℤ) - 1)).eval₂ (Int.castRingHom ℝ)
          ((x + x⁻¹) / 2) =
      ((x⁻¹) ^ d - x ^ d) / 2 := by
  induction d using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more d ih0 ih1 =>
    have hi2 : ((d + 2 : ℕ) : ℤ) - 1 = (d : ℤ) + 1 := by omega
    have hi1 : ((d + 1 : ℕ) : ℤ) - 1 = (d : ℤ) := by omega
    rw [hi1] at ih1
    rw [hi2, Chebyshev.U_add_one]
    simp only [eval₂_sub, eval₂_mul, eval₂_ofNat, eval₂_X]
    calc
      _ = 2 * ((x + x⁻¹) / 2) *
            (((x⁻¹ - x) / 2) *
              (Chebyshev.U ℤ (d : ℤ)).eval₂ (Int.castRingHom ℝ) ((x + x⁻¹) / 2)) -
          ((x⁻¹ - x) / 2) *
            (Chebyshev.U ℤ ((d : ℤ) - 1)).eval₂ (Int.castRingHom ℝ)
              ((x + x⁻¹) / 2) := by ring
      _ = 2 * ((x + x⁻¹) / 2) * (((x⁻¹) ^ (d + 1) - x ^ (d + 1)) / 2) -
          ((x⁻¹) ^ d - x ^ d) / 2 := by rw [ih1, ih0]
      _ = _ := by
        simp only [pow_add, pow_one, pow_two]
        linear_combination ((x⁻¹) ^ d - x ^ d) / 2 * (mul_inv_cancel₀ hx)

theorem inv_realCoordinateInv {x : ℝ} (hx : x ≠ 0) :
    (realCoordinateInv x)⁻¹ = (x + x⁻¹) / 2 := by
  unfold realCoordinateInv
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp [hx]
  ring

theorem sqrt_div_realCoordinateInv {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    Real.sqrt (1 - realCoordinateInv x ^ 2) / realCoordinateInv x =
      (x⁻¹ - x) / 2 := by
  rw [sqrt_one_sub_realCoordinateInv_sq hx]
  unfold realCoordinateInv
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp [hx0]

theorem rowP_realCoordinateInv {N r : ℕ} (hN : 0 < N) (hr : r < n N)
    {x : ℝ} (hx : x ≠ 0) :
    (realPoly (rowP N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        ((x ^ rowDistance N r + (x⁻¹) ^ rowDistance N r) / 2) := by
  have ht : realCoordinateInv x ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx) (by positivity)
  unfold realPoly
  rw [← eval₂_eq_eval_map, rowP_eval₂ (Int.castRingHom ℝ) hN hr ht,
    inv_realCoordinateInv hx, chebyshevT_eval_sheet _ hx]

theorem rowD_realCoordinateInv {N r : ℕ} (hN : 0 < N) (hr : r < n N)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    Real.sqrt (1 - realCoordinateInv x ^ 2) / realCoordinateInv x *
        (realPoly (rowD N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        (Int.sign (rowOffset N r) : ℝ) *
          (((x⁻¹) ^ rowDistance N r - x ^ rowDistance N r) / 2) := by
  have ht : realCoordinateInv x ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) (by positivity)
  unfold realPoly
  rw [sqrt_div_realCoordinateInv hx hx0, ← eval₂_eq_eval_map,
    rowD_eval₂ (Int.castRingHom ℝ) hN hr ht, inv_realCoordinateInv hx0]
  calc
    _ = (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        (Int.sign (rowOffset N r) : ℝ) *
          (((x⁻¹ - x) / 2) *
            (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).eval₂ (Int.castRingHom ℝ)
              ((x + x⁻¹) / 2)) := by
      rw [show (Int.castRingHom ℝ) (Int.sign (rowOffset N r)) =
        (Int.sign (rowOffset N r) : ℝ) from rfl]
      ring
    _ = _ := by rw [chebyshevU_eval_sheet _ hx0]

private theorem sheet_natAbs_sum (m : ℤ) (x : ℝ) :
    x ^ m.natAbs + (x⁻¹) ^ m.natAbs = x ^ m + x ^ (-m) := by
  calc
    _ = x ^ (m.natAbs : ℤ) + x ^ (-(m.natAbs : ℤ)) := by
      simp only [zpow_neg, zpow_natCast, inv_pow]
    _ = _ := by
      rcases Int.natAbs_eq m with hm | hm
      · exact congrArg (fun z : ℤ => x ^ z + x ^ (-z)) hm.symm
      · calc
          _ = x ^ (-(m.natAbs : ℤ)) + x ^ (-(-(m.natAbs : ℤ))) := by
            rw [neg_neg]
            ring
          _ = _ := congrArg (fun z : ℤ => x ^ z + x ^ (-z)) hm.symm

private theorem sheet_natAbs_difference (m : ℤ) (x : ℝ) :
    (Int.sign m : ℝ) * ((x⁻¹) ^ m.natAbs - x ^ m.natAbs) =
      x ^ (-m) - x ^ m := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [Int.sign_eq_neg_one_of_neg hm]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
    calc
      _ = x ^ (m.natAbs : ℤ) - x ^ (-(m.natAbs : ℤ)) := by
        simp only [zpow_neg, zpow_natCast, inv_pow]
        ring
      _ = _ := by rw [Int.ofNat_natAbs_of_nonpos hm.le, neg_neg]
  · subst m
    simp
  · rw [Int.sign_eq_one_of_pos hm]
    simp only [Int.cast_one, one_mul]
    calc
      _ = x ^ (-(m.natAbs : ℤ)) - x ^ (m.natAbs : ℤ) := by
        simp only [zpow_neg, zpow_natCast, inv_pow]
      _ = _ := by rw [Int.natAbs_of_nonneg hm.le]

theorem rowP_realCoordinateInv_signed {N r : ℕ} (hN : 0 < N) (hr : r < n N)
    {x : ℝ} (hx : x ≠ 0) :
    (realPoly (rowP N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        ((x ^ rowOffset N r + x ^ (-rowOffset N r)) / 2) := by
  simpa only [rowDistance, sheet_natAbs_sum] using rowP_realCoordinateInv hN hr hx

theorem rowD_realCoordinateInv_signed {N r : ℕ} (hN : 0 < N) (hr : r < n N)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    Real.sqrt (1 - realCoordinateInv x ^ 2) / realCoordinateInv x *
        (realPoly (rowD N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        ((x ^ (-rowOffset N r) - x ^ rowOffset N r) / 2) := by
  rw [rowD_realCoordinateInv hN hr hx hx0]
  calc
    _ = (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        (((Int.sign (rowOffset N r) : ℝ) *
          ((x⁻¹) ^ rowDistance N r - x ^ rowDistance N r)) / 2) := by ring
    _ = _ := by rw [rowDistance, sheet_natAbs_difference]

theorem realRowAmplitude_sheet {N r : ℕ} (hN : 0 < N) (hr : r < n N)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    realRowAmplitude N r (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        (if x < 0 then
          (1 / 2 : ℝ) * x ^ (-rowOffset N r) + (1 / 2 : ℝ) * x ^ rowOffset N r
        else
          -(1 / 4 : ℝ) * x ^ (-rowOffset N r) + (5 / 4 : ℝ) * x ^ rowOffset N r) := by
  by_cases hn : x < 0
  · have ht : realCoordinateInv x < 0 := by
      unfold realCoordinateInv
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hn) (by positivity)
    rw [realRowAmplitude_of_neg N r ht, rowP_realCoordinateInv_signed hN hr hx0, if_pos hn]
    ring
  · have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx0)
    have ht : 0 < realCoordinateInv x := by
      unfold realCoordinateInv
      exact div_pos (mul_pos (by norm_num) hp) (by positivity)
    rw [realRowAmplitude_of_pos N r ht, rowP_realCoordinateInv_signed hN hr hx0,
      rowD_realCoordinateInv_signed hN hr hx hx0, if_neg hn]
    ring

end

section

open Set
open scoped BigOperators

def realSheetDeterminant (N : ℕ) (x : Fin (n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (n N) =>
    if x i < 0 then
      (1 / 2 : ℝ) * (x i) ^ (-rowOffset N r.val) +
        (1 / 2 : ℝ) * (x i) ^ rowOffset N r.val
    else
      -(1 / 4 : ℝ) * (x i) ^ (-rowOffset N r.val) +
        (5 / 4 : ℝ) * (x i) ^ rowOffset N r.val))

theorem realRowAmplitude_det_eq_sheet {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    Matrix.det (Matrix.of (fun r i : Fin (n N) =>
      realRowAmplitude N r.val (realCoordinateInv (x i)))) =
        realSheetDeterminant N x *
          ∏ i : Fin (n N), realCoordinateInv (x i) ^ (Cdegree N - 1) *
            (1 - realCoordinateInv (x i)) ^ h N := by
  classical
  let weight : Fin (n N) → ℝ := fun i =>
    realCoordinateInv (x i) ^ (Cdegree N - 1) * (1 - realCoordinateInv (x i)) ^ h N
  let A : Matrix (Fin (n N)) (Fin (n N)) ℝ := Matrix.of (fun r i =>
    if x i < 0 then
      (1 / 2 : ℝ) * (x i) ^ (-rowOffset N r.val) +
        (1 / 2 : ℝ) * (x i) ^ rowOffset N r.val
    else
      -(1 / 4 : ℝ) * (x i) ^ (-rowOffset N r.val) +
        (5 / 4 : ℝ) * (x i) ^ rowOffset N r.val)
  have hmatrix :
      Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (realCoordinateInv (x i))) =
        Matrix.of (fun r i : Fin (n N) => weight i * A r i) := by
    funext r i
    change realRowAmplitude N r.val (realCoordinateInv (x i)) = weight i * A r i
    rw [realRowAmplitude_sheet hN r.isLt (hx i) (hx0 i)]
    dsimp only [weight, A, Matrix.of_apply]
    ring
  rw [hmatrix, Matrix.det_mul_row]
  change (∏ i : Fin (n N), weight i) * realSheetDeterminant N x =
    realSheetDeterminant N x * (∏ i : Fin (n N), weight i)
  exact mul_comm _ _

end

section

open scoped BigOperators

def realFirstSheetMixedMatrix (N : ℕ) (x : Fin (n N) → ℝ) :
    Matrix (Fin (n N)) (Fin (n N)) ℝ :=
  Matrix.of (fun r i =>
    (x i) ^ r.rev.val +
      (if x i < 0 then (x i) ^ (n N - 1 - 2 * g N)
        else -5 * (x i) ^ (n N - 1 - 2 * g N)) * (x i) ^ r.val)

theorem realFirstSheet_far_monomial {N : ℕ} (hN : 0 < N)
    (r : Fin (n N)) {x : ℝ} (hx : x ≠ 0) :
    x ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) * x ^ r.rev.val =
      x ^ (-rowOffset N r.val) := by
  calc
    _ = x ^ (((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) + (r.rev.val : ℤ)) := by
      rw [zpow_add₀ hx, zpow_natCast]
    _ = x ^ (-rowOffset N r.val) := by
      congr 1
      have hr := r.isLt
      simp only [Fin.val_rev]
      unfold rowOffset n g at *
      omega

theorem realFirstSheet_near_monomial {N : ℕ} (hN : 0 < N)
    (r : Fin (n N)) {x : ℝ} (hx : x ≠ 0) :
    x ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) *
        (x ^ (n N - 1 - 2 * g N) * x ^ r.val) =
      x ^ rowOffset N r.val := by
  calc
    _ = x ^ ((((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) +
        ((n N - 1 - 2 * g N : ℕ) : ℤ)) + (r.val : ℤ)) := by
      simp only [zpow_add₀ hx, zpow_natCast]
      ring
    _ = x ^ rowOffset N r.val := by
      congr 1
      unfold rowOffset n g
      omega

theorem realFirstSheet_entry_factor {N : ℕ} (hN : 0 < N)
    (r : Fin (n N)) {x : ℝ} (hx : x ≠ 0) :
    (if x < 0 then
      (1 / 2 : ℝ) * x ^ (-rowOffset N r.val) +
        (1 / 2 : ℝ) * x ^ rowOffset N r.val
    else
      -(1 / 4 : ℝ) * x ^ (-rowOffset N r.val) +
        (5 / 4 : ℝ) * x ^ rowOffset N r.val) =
      (if x < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
        x ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) *
          (x ^ r.rev.val +
            (if x < 0 then x ^ (n N - 1 - 2 * g N)
              else -5 * x ^ (n N - 1 - 2 * g N)) * x ^ r.val) := by
  by_cases hneg : x < 0
  · simp only [if_pos hneg]
    rw [← realFirstSheet_far_monomial hN r hx,
      ← realFirstSheet_near_monomial hN r hx]
    ring
  · simp only [if_neg hneg]
    rw [← realFirstSheet_far_monomial hN r hx,
      ← realFirstSheet_near_monomial hN r hx]
    ring

theorem realSheetDeterminant_firstSheet_factor {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ≠ 0) :
    realSheetDeterminant N x =
      (∏ i, (if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
        (x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
          Matrix.det (realFirstSheetMixedMatrix N x) := by
  classical
  unfold realSheetDeterminant
  have hmatrix :
      Matrix.of (fun r i : Fin (n N) =>
        if x i < 0 then
          (1 / 2 : ℝ) * (x i) ^ (-rowOffset N r.val) +
            (1 / 2 : ℝ) * (x i) ^ rowOffset N r.val
        else
          -(1 / 4 : ℝ) * (x i) ^ (-rowOffset N r.val) +
            (5 / 4 : ℝ) * (x i) ^ rowOffset N r.val) =
        Matrix.of (fun r i : Fin (n N) =>
          ((if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
            (x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
              realFirstSheetMixedMatrix N x r i) := by
    ext r i
    exact realFirstSheet_entry_factor hN r (hx i)
  rw [hmatrix, Matrix.det_mul_row]

theorem realFirstSheet_far_coefficient_abs_le (x : ℝ) :
    |if x < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)| ≤ 1 := by
  by_cases hx : x < 0 <;> norm_num [hx]

theorem realFirstSheet_factor_abs_le (N : ℕ) (x : Fin (n N) → ℝ) :
    |∏ i, (if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
      (x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))| ≤
        ∏ i, |(x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))| := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_mul]
    calc
      _ ≤ 1 * |(x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))| :=
        mul_le_mul_of_nonneg_right (realFirstSheet_far_coefficient_abs_le (x i))
          (abs_nonneg _)
      _ = _ := one_mul _

theorem realFirstSheet_factor_abs_le_weight (N : ℕ) (x : Fin (n N) → ℝ) :
    |∏ i, (if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
      (x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))| ≤
        ∏ i, |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) := by
  simpa only [abs_zpow] using realFirstSheet_factor_abs_le N x

theorem realSheetDeterminant_abs_le_firstSheet_mixed {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ≠ 0) :
    |realSheetDeterminant N x| ≤
      (∏ i, |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
        |Matrix.det (realFirstSheetMixedMatrix N x)| := by
  rw [realSheetDeterminant_firstSheet_factor hN x hx, abs_mul]
  exact mul_le_mul_of_nonneg_right (realFirstSheet_factor_abs_le_weight N x)
    (abs_nonneg _)

end

section

open Set

section

private theorem sqrt_one_add_inv_sq {x : ℝ} (hx0 : x ≠ 0) :
    Real.sqrt (1 + (x⁻¹) ^ 2) = Real.sqrt (1 + x ^ 2) / |x| := by
  have heq : 1 + (x⁻¹) ^ 2 = (1 + x ^ 2) / x ^ 2 := by
    field_simp [hx0]
    ring
  rw [heq, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs]

theorem sheet_far_weight_eq (N : ℕ) {x : ℝ} (hx0 : x ≠ 0) :
    |(x⁻¹) ^ (-(g N : ℤ))| * Real.sqrt (1 + (x⁻¹) ^ 2) ^ (n N - 1) =
      Real.sqrt (1 + x ^ 2) ^ (n N - 1) *
        |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) := by
  rw [abs_zpow, abs_inv, sqrt_one_add_inv_sq hx0]
  simp only [zpow_neg, zpow_natCast, inv_pow, inv_inv, div_pow]
  rw [zpow_sub₀ (abs_ne_zero.mpr hx0)]
  simp only [zpow_natCast]
  ring

theorem sheet_near_weight_le {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    |x ^ (-(g N : ℤ))| * Real.sqrt (1 + x ^ 2) ^ (n N - 1) ≤
      Real.sqrt (1 + x ^ 2) ^ (n N - 1) *
        |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) := by
  have hdim : 2 * g N ≤ n N - 1 := by
    unfold g n
    omega
  have hexp : (g N : ℤ) - ((n N - 1 : ℕ) : ℤ) ≤ -(g N : ℤ) := by omega
  have hp := zpow_le_zpow_right_of_le_one₀ (abs_pos.mpr hx0)
    (abs_lt.mpr hx).le hexp
  rw [abs_zpow, mul_comm]
  exact mul_le_mul_of_nonneg_left hp (pow_nonneg (Real.sqrt_nonneg _) _)

theorem sheet_choice_weight_le {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) (ε : Bool) :
    let z := if ε then x else x⁻¹
    |z ^ (-(g N : ℤ))| * Real.sqrt (1 + z ^ 2) ^ (n N - 1) ≤
      Real.sqrt (1 + x ^ 2) ^ (n N - 1) *
        |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) := by
  cases ε
  · simpa using (sheet_far_weight_eq N hx0).le
  · simpa using sheet_near_weight_le hN hx hx0

end

open Set
open scoped BigOperators

def realSheetCoefficient (x : ℝ) (near : Bool) : ℝ :=
  if x < 0 then 1 / 2 else if near then 5 / 4 else -(1 / 4)

def realSheetNode (x : ℝ) (near : Bool) : ℝ :=
  if near then x else x⁻¹

theorem det_column_sum_bool {m : ℕ}
    (A : Bool → Matrix (Fin m) (Fin m) ℝ) :
    Matrix.det (Matrix.of (fun r i : Fin m => ∑ b : Bool, A b r i)) =
      ∑ ε : Fin m → Bool,
        Matrix.det (Matrix.of (fun r i : Fin m => A (ε i) r i)) := by
  classical
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]

theorem realSheetDeterminant_eq_sum (N : ℕ) (x : Fin (n N) → ℝ) :
    realSheetDeterminant N x =
      ∑ ε : Fin (n N) → Bool,
        (∏ i, realSheetCoefficient (x i) (ε i)) *
          Matrix.det (Matrix.of (fun r i : Fin (n N) =>
            realSheetNode (x i) (ε i) ^ rowOffset N r.val)) := by
  classical
  have hmatrix :
      Matrix.of (fun r i : Fin (n N) =>
        if x i < 0 then
          (1 / 2 : ℝ) * (x i) ^ (-rowOffset N r.val) +
            (1 / 2 : ℝ) * (x i) ^ rowOffset N r.val
        else
          -(1 / 4 : ℝ) * (x i) ^ (-rowOffset N r.val) +
            (5 / 4 : ℝ) * (x i) ^ rowOffset N r.val) =
        Matrix.of (fun r i : Fin (n N) => ∑ b : Bool,
          realSheetCoefficient (x i) b *
            realSheetNode (x i) b ^ rowOffset N r.val) := by
    ext r i
    by_cases hi : x i < 0 <;>
      simp [realSheetCoefficient, realSheetNode, hi, zpow_neg] <;> ring
  unfold realSheetDeterminant
  rw [hmatrix]
  have hexpand := det_column_sum_bool (fun b => Matrix.of (fun r i : Fin (n N) =>
    realSheetCoefficient (x i) b * realSheetNode (x i) b ^ rowOffset N r.val))
  simp only [Matrix.of_apply] at hexpand
  rw [hexpand]
  apply Finset.sum_congr rfl
  intro ε _
  simpa only [Matrix.of_apply] using
    Matrix.det_mul_row (fun i => realSheetCoefficient (x i) (ε i))
      (Matrix.of (fun r i : Fin (n N) =>
        realSheetNode (x i) (ε i) ^ rowOffset N r.val))

theorem realSheetCoefficient_abs_sum_le (x : ℝ) :
    (∑ b : Bool, |realSheetCoefficient x b|) ≤ (3 / 2 : ℝ) := by
  by_cases hx : x < 0 <;>
    norm_num [realSheetCoefficient, hx, Fintype.sum_bool]

theorem realSheetCoefficient_sum_abs_prod_le (N : ℕ) (x : Fin (n N) → ℝ) :
    (∑ ε : Fin (n N) → Bool,
      |∏ i, realSheetCoefficient (x i) (ε i)|) ≤ (3 / 2 : ℝ) ^ n N := by
  classical
  calc
    _ = ∏ i, ∑ b : Bool, |realSheetCoefficient (x i) b| := by
      simp only [Finset.abs_prod]
      exact (Fintype.prod_sum (fun i b => |realSheetCoefficient (x i) b|)).symm
    _ ≤ ∏ _i : Fin (n N), (3 / 2 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      · intro i _
        exact realSheetCoefficient_abs_sum_le (x i)
    _ = (3 / 2 : ℝ) ^ n N := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem laurent_monomial_det_eq {m : ℕ} (g : ℕ) (z : Fin m → ℝ)
    (hz : ∀ i, z i ≠ 0) :
    Matrix.det (Matrix.of (fun r i : Fin m => z i ^ ((r.val : ℤ) - (g : ℤ)))) =
      (∏ i, z i ^ (-(g : ℤ))) * Matrix.det (Matrix.vandermonde z) := by
  have hmatrix :
      Matrix.of (fun r i : Fin m => z i ^ ((r.val : ℤ) - (g : ℤ))) =
        Matrix.of (fun r i : Fin m =>
          z i ^ (-(g : ℤ)) * (Matrix.vandermonde z).transpose r i) := by
    ext r i
    simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      sub_eq_add_neg, zpow_add₀ (hz i), zpow_natCast]
    ring
  rw [hmatrix, Matrix.det_mul_row, Matrix.det_transpose]

theorem laurent_monomial_det_abs_le {m : ℕ} (g : ℕ) (z : Fin m → ℝ)
    (hz : ∀ i, z i ≠ 0) :
    |Matrix.det (Matrix.of (fun r i : Fin m => z i ^ ((r.val : ℤ) - (g : ℤ))))| ≤
      (Real.sqrt (m : ℝ)) ^ m / (2 : ℝ) ^ (m.choose 2) *
        ∏ i, (|z i ^ (-(g : ℤ))| * Real.sqrt (1 + z i ^ 2) ^ (m - 1)) := by
  rw [laurent_monomial_det_eq g z hz, abs_mul, Finset.abs_prod, Matrix.det_vandermonde]
  calc
    _ ≤ (∏ i, |z i ^ (-(g : ℤ))|) *
        ((Real.sqrt (m : ℝ)) ^ m / (2 : ℝ) ^ (m.choose 2) *
          ∏ i, Real.sqrt (1 + z i ^ 2) ^ (m - 1)) :=
      mul_le_mul_of_nonneg_left (weighted_real_vandermonde_le_sqrt z)
        (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      ring

theorem realSheetDeterminant_abs_le_of_monomial_bound (N : ℕ)
    (x : Fin (n N) → ℝ) (B : ℝ)
    (hB : ∀ ε : Fin (n N) → Bool,
      |Matrix.det (Matrix.of (fun r i : Fin (n N) =>
        realSheetNode (x i) (ε i) ^ rowOffset N r.val))| ≤ B) :
    |realSheetDeterminant N x| ≤ (3 / 2 : ℝ) ^ n N * B := by
  classical
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (fun _ => false))
  rw [realSheetDeterminant_eq_sum]
  calc
    _ ≤ ∑ ε : Fin (n N) → Bool,
        |(∏ i, realSheetCoefficient (x i) (ε i)) *
          Matrix.det (Matrix.of (fun r i : Fin (n N) =>
            realSheetNode (x i) (ε i) ^ rowOffset N r.val))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ε : Fin (n N) → Bool,
        |∏ i, realSheetCoefficient (x i) (ε i)| * B := by
      apply Finset.sum_le_sum
      intro ε _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB ε) (abs_nonneg _)
    _ = (∑ ε : Fin (n N) → Bool,
        |∏ i, realSheetCoefficient (x i) (ε i)|) * B := by rw [Finset.sum_mul]
    _ ≤ (3 / 2 : ℝ) ^ n N * B :=
      mul_le_mul_of_nonneg_right (realSheetCoefficient_sum_abs_prod_le N x) hB0

theorem realSheetDeterminant_abs_le_sqrt {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    |realSheetDeterminant N x| ≤
      (3 / 2 : ℝ) ^ n N * (Real.sqrt (n N : ℝ)) ^ n N /
        (2 : ℝ) ^ ((n N).choose 2) *
        ∏ i, (Real.sqrt (1 + x i ^ 2) ^ (n N - 1) *
          |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) := by
  classical
  let C : ℝ := (Real.sqrt (n N : ℝ)) ^ n N / (2 : ℝ) ^ ((n N).choose 2)
  let W : Fin (n N) → ℝ := fun i =>
    Real.sqrt (1 + x i ^ 2) ^ (n N - 1) *
      |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))
  have hchoice (ε : Fin (n N) → Bool) :
      |Matrix.det (Matrix.of (fun r i : Fin (n N) =>
        realSheetNode (x i) (ε i) ^ rowOffset N r.val))| ≤ C * ∏ i, W i := by
    let z : Fin (n N) → ℝ := fun i => realSheetNode (x i) (ε i)
    have hz (i : Fin (n N)) : z i ≠ 0 := by
      dsimp only [z, realSheetNode]
      split_ifs
      · exact hx0 i
      · exact inv_ne_zero (hx0 i)
    have hmon := laurent_monomial_det_abs_le (g N) z hz
    change |Matrix.det (Matrix.of (fun r i : Fin (n N) =>
      z i ^ ((r.val : ℤ) - (g N : ℤ))))| ≤ C * ∏ i, W i
    apply hmon.trans
    apply mul_le_mul_of_nonneg_left
    · apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg (abs_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
      · intro i _
        simpa only [z, realSheetNode, W] using
          sheet_choice_weight_le hN (hx i) (hx0 i) (ε i)
    · positivity
  have h := realSheetDeterminant_abs_le_of_monomial_bound N x (C * ∏ i, W i) hchoice
  calc
    |realSheetDeterminant N x| ≤ (3 / 2 : ℝ) ^ n N * (C * ∏ i, W i) := h
    _ = _ := by dsimp only [C, W]; ring

end

section

open Set
open scoped BigOperators

theorem realSheetDeterminant_abs_le {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    |realSheetDeterminant N x| ≤
      (3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) /
        (2 : ℝ) ^ ((n N).choose 2) *
        (∏ i : Fin (n N),
          ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) *
            |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)))) := by
  have hdim : 1 ≤ n N := by unfold n; omega
  have hcast : ((n N - 1 : ℕ) : ℝ) = (n N : ℝ) - 1 := by
    rw [Nat.cast_sub hdim, Nat.cast_one]
  have hhead : Real.sqrt (n N : ℝ) ^ n N = (n N : ℝ) ^ ((n N : ℝ) / 2) := by
    symm
    simpa only [Real.rpow_natCast] using
      Real.rpow_div_two_eq_sqrt (n N : ℝ) (Nat.cast_nonneg (n N))
  have hrow (i : Fin (n N)) :
      Real.sqrt (1 + x i ^ 2) ^ (n N - 1) =
        (1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) := by
    symm
    have h := Real.rpow_div_two_eq_sqrt ((n N - 1 : ℕ) : ℝ)
      (by positivity : (0 : ℝ) ≤ 1 + x i ^ 2)
    rw [Real.rpow_natCast] at h
    simpa only [hcast] using h
  simpa only [hhead, hrow] using realSheetDeterminant_abs_le_sqrt hN x hx hx0

end

open MeasureTheory Set
open scoped BigOperators

def sheetRealIntegrand (N : ℕ) (x s : Fin (n N) → ℝ) : ℝ :=
  realSheetDeterminant N x *
    (∏ i : Fin (n N), realCoordinateInv (x i) ^ (Cdegree N - 1) *
      (1 - realCoordinateInv (x i)) ^ h N) *
    (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i,
      (realCoordinateInv (x j) - realCoordinateInv (x i))) *
    (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)) ^ 2 *
    (∏ j : Fin (n N), (s j) ^ b N * (1 - s j) ^ q N) /
    (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - realCoordinateInv (x i) * s j))

theorem coordinate_productRealIntegrand_eq_sheet {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    productRealIntegrand N (fun i => realCoordinateInv (x i)) s =
      sheetRealIntegrand N x s := by
  unfold productRealIntegrand sheetRealIntegrand
  rw [realRowAmplitude_det_eq_sheet hN x hx hx0]

theorem ae_coordinate_productRealIntegrand_eq_sheet {N : ℕ} (hN : 0 < N) :
    (fun p => productRealIntegrand N (fun i => realCoordinateInv (p.1 i)) p.2)
      =ᵐ[realCoordinateListPairMeasure N] (fun p => sheetRealIntegrand N p.1 p.2) := by
  have hreg : ∀ᵐ p ∂realCoordinateListPairMeasure N,
      ∀ i, p.1 i ∈ Ioo (-1 : ℝ) 1 ∧ p.1 i ≠ 0 := by
    exact (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure))
      (ν := Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))).tendsto_ae.eventually
        (ae_realCoordinate_list_regular N)
  filter_upwards [hreg] with p hp
  exact coordinate_productRealIntegrand_eq_sheet hN p.1 p.2
    (fun i => (hp i).1) (fun i => (hp i).2)

theorem integrable_sheetRealIntegrand {N : ℕ} (hN : 0 < N) :
    Integrable (fun p => sheetRealIntegrand N p.1 p.2)
      (realCoordinateListPairMeasure N) :=
  (integrable_coordinate_productRealIntegrand N).congr
    (ae_coordinate_productRealIntegrand_eq_sheet hN)

theorem determinant_eq_sheetRealIntegral {N : ℕ} (hN : 0 < N) :
    determinant N = 1 / (((n N).factorial : ℝ) ^ 2) *
      ∫ x, (∫ s, sheetRealIntegrand N x s
        ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))
        ∂Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure) := by
  rw [determinant_eq_coordinateProductIntegral N]
  congr 1
  calc
    _ = ∫ p, productRealIntegrand N (fun i => realCoordinateInv (p.1 i)) p.2
        ∂realCoordinateListPairMeasure N :=
      (integral_prod _ (integrable_coordinate_productRealIntegrand N)).symm
    _ = ∫ p, sheetRealIntegrand N p.1 p.2 ∂realCoordinateListPairMeasure N :=
      integral_congr_ae (ae_coordinate_productRealIntegrand_eq_sheet hN)
    _ = _ := integral_prod _ (integrable_sheetRealIntegrand hN)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealEnergyTwoProduct
namespace OAI

noncomputable section

namespace InternalCatalan

section

open scoped BigOperators

theorem energy_row_weight_coordinate (p q : ℕ) (x : ℝ) :
    |realCoordinateInv x| ^ p * (1 - realCoordinateInv x) ^ q =
      (2 : ℝ) ^ p * |x| ^ p * (1 - x) ^ (2 * q) /
        (1 + x ^ 2) ^ (p + q) := by
  rw [abs_realCoordinateInv, one_sub_realCoordinateInv]
  simp only [div_pow, mul_pow, pow_add, pow_mul]
  ring

theorem prod_energy_row_weight_coordinate (N : ℕ) (x : Fin (n N) → ℝ) :
    (∏ i : Fin (n N),
      (|realCoordinateInv (x i)| ^ (Cdegree N - 1) *
        (1 - realCoordinateInv (x i)) ^ h N)) =
      (2 : ℝ) ^ (n N * (Cdegree N - 1)) *
        (∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) /
        (∏ i : Fin (n N), (1 + x i ^ 2) ^ (Cdegree N - 1 + h N)) := by
  simp_rw [energy_row_weight_coordinate]
  simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_fin]
  rw [← pow_mul, Nat.mul_comm (Cdegree N - 1) (n N)]
  ring

theorem energy_quadratic_weight_cancel {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (1 + x ^ 2) ^ n N /
      ((1 + x ^ 2) ^ (n N - 1) *
        (1 + x ^ 2) ^ (Cdegree N - 1 + h N)) =
      1 / (1 + x ^ 2) ^ (H N - 2) := by
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (realCoordinateInv_denominator_pos x)
  have he : (n N - 1) + (Cdegree N - 1 + h N) = n N + (H N - 2) := by
    unfold n Cdegree h H
    omega
  rw [← pow_add, he, pow_add]
  field_simp

theorem prod_energy_quadratic_weight_cancel {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) :
    (∏ i : Fin (n N), (1 + x i ^ 2) ^ n N) /
      ((∏ i : Fin (n N), (1 + x i ^ 2) ^ (n N - 1)) *
        (∏ i : Fin (n N), (1 + x i ^ 2) ^ (Cdegree N - 1 + h N))) =
      1 / (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  simp_rw [energy_quadratic_weight_cancel hN]
  simp only [Finset.prod_div_distrib, Finset.prod_const_one]

theorem energy_abs_node_weight_cancel {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx0 : x ≠ 0) :
    |x| ^ (Cdegree N - 1) *
      |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) = |x| ^ A N := by
  have he : ((Cdegree N - 1 : ℕ) : ℤ) +
      ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) = (A N : ℤ) := by
    rw [← add_sub_assoc]
    exact energy_abs_node_exponent hN
  calc
    _ = |x| ^ (((Cdegree N - 1 : ℕ) : ℤ) +
        ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) := by
      rw [zpow_add₀ (abs_ne_zero.mpr hx0), zpow_natCast]
    _ = |x| ^ A N := by rw [he, zpow_natCast]

end

open Set
open scoped BigOperators

def realPrincipalIntegrand (N : ℕ) (x s : Fin (n N) → ℝ) : ℝ :=
  (|∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i,
      (realCoordinateInv (x j) - realCoordinateInv (x i))| *
    |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 /
    (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - realCoordinateInv (x i) * s j))) *
    (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) *
    (∏ i : Fin (n N), (|realCoordinateInv (x i)| ^ (Cdegree N - 1) *
      (1 - realCoordinateInv (x i)) ^ h N))

def realEnergyMajorantOne (N : ℕ) (x s : Fin (n N) → ℝ) : ℝ :=
  realPrincipalIntegrand N x s / (2 : ℝ) ^ ((n N).choose 2) *
    (∏ i : Fin (n N), ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) *
      |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))))

def realEnergyMajorantTwo (N : ℕ) (x s : Fin (n N) → ℝ) : ℝ :=
  realPrincipalIntegrand N x s *
    |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
    (∏ i : Fin (n N), |x i| ^ g N)

private theorem principal_kernel_product_pos (N : ℕ) (x s : Fin (n N) → ℝ)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    0 < ∏ i : Fin (n N), ∏ j : Fin (n N), (1 - realCoordinateInv (x i) * s j) := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact realCoordinateInv_kernel_pos (x i) (hs j)

private theorem principal_s_weight_pos (N : ℕ) (s : Fin (n N) → ℝ)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    0 < ∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N) := by
  apply Finset.prod_pos
  intro j _
  exact mul_pos (pow_pos (hs j).1 _) (pow_pos (sub_pos.mpr (hs j).2) _)

private theorem principal_t_weight_nonneg (N : ℕ) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ ∏ i : Fin (n N), (|realCoordinateInv (x i)| ^ (Cdegree N - 1) *
      (1 - realCoordinateInv (x i)) ^ h N) := by
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (pow_nonneg (one_sub_realCoordinateInv_pos (hx i)).le _)

theorem realPrincipalIntegrand_nonneg (N : ℕ) (x s : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    0 ≤ realPrincipalIntegrand N x s := by
  unfold realPrincipalIntegrand
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
        (principal_kernel_product_pos N x s hs).le)
      (principal_s_weight_pos N s hs).le)
    (principal_t_weight_nonneg N x hx)


theorem abs_sheetRealIntegrand_eq (N : ℕ) (x s : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    |sheetRealIntegrand N x s| = |realSheetDeterminant N x| * realPrincipalIntegrand N x s := by
  have htw : |∏ i : Fin (n N),
      (realCoordinateInv (x i) ^ (Cdegree N - 1) *
        (1 - realCoordinateInv (x i)) ^ h N)| =
      ∏ i : Fin (n N), (|realCoordinateInv (x i)| ^ (Cdegree N - 1) *
        (1 - realCoordinateInv (x i)) ^ h N) := by
    rw [Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp only [abs_mul, abs_pow, abs_of_pos (one_sub_realCoordinateInv_pos (hx i))]
  unfold sheetRealIntegrand realPrincipalIntegrand
  simp only [abs_div, abs_mul, abs_pow, htw,
    abs_of_pos (principal_kernel_product_pos N x s hs),
    abs_of_pos (principal_s_weight_pos N s hs)]
  ring

theorem abs_sheetRealIntegrand_le_majorantOne {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    |sheetRealIntegrand N x s| ≤
      (3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) *
        realEnergyMajorantOne N x s := by
  rw [abs_sheetRealIntegrand_eq N x s hx hs]
  calc
    _ ≤ ((3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) /
        (2 : ℝ) ^ ((n N).choose 2) *
        (∏ i : Fin (n N), ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) *
          |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))))) *
          realPrincipalIntegrand N x s :=
      mul_le_mul_of_nonneg_right (realSheetDeterminant_abs_le hN x hx hx0)
        (realPrincipalIntegrand_nonneg N x s hx hs)
    _ = _ := by
      unfold realEnergyMajorantOne
      ring

theorem realPrincipalIntegrand_coordinate {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    realPrincipalIntegrand N x s =
      (2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2) *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
        (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
        (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) *
        (∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) /
        ((∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2)) *
          (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2))) := by
  unfold realPrincipalIntegrand
  rw [abs_vandermonde_realCoordinateInv x hx, prod_realCoordinateInv_kernel,
    prod_energy_row_weight_coordinate]
  calc
    _ = ((2 : ℝ) ^ ((n N).choose 2) * (2 : ℝ) ^ (n N * (Cdegree N - 1)) *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
          (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
          (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) *
          (∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) /
          (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2))) *
        ((∏ i : Fin (n N), (1 + x i ^ 2) ^ n N) /
          ((∏ i : Fin (n N), (1 + x i ^ 2) ^ (n N - 1)) *
            (∏ i : Fin (n N), (1 + x i ^ 2) ^ (Cdegree N - 1 + h N)))) := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ = _ := by
      rw [prod_energy_quadratic_weight_cancel hN x, pow_add]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem energy_one_quadratic_weight {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (1 + x ^ 2) ^ (((n N : ℝ) - 1) / 2) / (1 + x ^ 2) ^ (H N - 2) =
      (1 + x ^ 2) ^
        (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2) := by
  have hH : 2 ≤ H N := by unfold H; omega
  have hc : ((H N - 2 : ℕ) : ℝ) = (Cdegree N : ℝ) + (h N : ℝ) - 2 := by
    rw [Nat.cast_sub hH, H_eq_Cdegree_add_h, Nat.cast_add, Nat.cast_ofNat]
  rw [← Real.rpow_sub_natCast (realCoordinateInv_denominator_pos x).ne']
  congr 1
  rw [hc]
  ring

theorem realEnergyMajorantOne_coordinate {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    realEnergyMajorantOne N x s =
      (2 : ℝ) ^ (n N * (Cdegree N - 1)) *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
        (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
        (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) *
        (∏ i : Fin (n N),
          (|x i| ^ A N * (1 - x i) ^ (2 * h N) *
            (1 + x i ^ 2) ^
              (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2))) /
        (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2)) := by
  have hw :
      ((∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
        (∏ i : Fin (n N), ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) *
          |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))))) /
          (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2)) =
        ∏ i : Fin (n N),
          (|x i| ^ A N * (1 - x i) ^ (2 * h N) *
            (1 + x i ^ 2) ^
              (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    calc
      _ = (|x i| ^ (Cdegree N - 1) *
            |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
          (1 - x i) ^ (2 * h N) *
          ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) /
            (1 + x i ^ 2) ^ (H N - 2)) := by ring
      _ = _ := by rw [energy_abs_node_weight_cancel hN (hx0 i),
        energy_one_quadratic_weight hN]
  unfold realEnergyMajorantOne
  rw [realPrincipalIntegrand_coordinate hN x s hx]
  calc
    _ = ((2 : ℝ) ^ (n N * (Cdegree N - 1)) *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
          (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
          (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) /
          (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2))) *
        ((2 : ℝ) ^ ((n N).choose 2) / (2 : ℝ) ^ ((n N).choose 2)) *
        (((∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
          (∏ i : Fin (n N), ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) *
            |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))))) /
          (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2))) := by
      rw [pow_add]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [div_self (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), mul_one, hw]
      ring

open Set
open scoped BigOperators

theorem energy_abs_node_weight_two_cancel {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx0 : x ≠ 0) :
    (|x| ^ (Cdegree N - 1) * |x| ^ g N) / |x| ^ (n N - 1) = |x| ^ A N := by
  calc
    _ = |x| ^ (Cdegree N - 1) *
        |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) := by
      rw [zpow_sub₀ (abs_ne_zero.mpr hx0)]
      simp only [zpow_natCast]
      ring
    _ = |x| ^ A N := energy_abs_node_weight_cancel hN hx0

theorem prod_energy_abs_node_weight_two_cancel {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx0 : ∀ i, x i ≠ 0) :
    ((∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
      (∏ i : Fin (n N), |x i| ^ g N)) /
        (∏ i : Fin (n N), |x i| ^ (n N - 1)) =
      ∏ i : Fin (n N), (|x i| ^ A N * (1 - x i) ^ (2 * h N)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  calc
    _ = ((|x i| ^ (Cdegree N - 1) * |x i| ^ g N) / |x i| ^ (n N - 1)) *
        (1 - x i) ^ (2 * h N) := by ring
    _ = _ := by rw [energy_abs_node_weight_two_cancel hN (hx0 i)]

theorem realEnergyMajorantTwo_coordinate {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    realEnergyMajorantTwo N x s =
      (2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2) *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| ^ 2 *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
        (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
        (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) *
        (∏ i : Fin (n N), (|x i| ^ A N * (1 - x i) ^ (2 * h N))) /
        ((∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2)) *
          (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2))) := by
  unfold realEnergyMajorantTwo
  rw [realPrincipalIntegrand_coordinate hN x s hx, abs_vandermonde_inv x hx0]
  calc
    _ = ((2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2) *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (x j - x i)| ^ 2 *
          |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)| ^ 2 *
          (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) *
          (∏ j : Fin (n N), (s j ^ b N * (1 - s j) ^ q N)) /
          ((∏ i : Fin (n N), ∏ j : Fin (n N), (1 - 2 * x i * s j + x i ^ 2)) *
            (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2)))) *
        (((∏ i : Fin (n N), (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
          (∏ i : Fin (n N), |x i| ^ g N)) /
            (∏ i : Fin (n N), |x i| ^ (n N - 1))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [prod_energy_abs_node_weight_two_cancel hN x hx0]
      ring

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.RealEnergyLogMajorants
namespace OAI

noncomputable section

namespace InternalCatalan

open Set
open scoped BigOperators

private theorem energy_difference_ne_zero_of_lt {m : ℕ} (x : Fin m → ℝ)
    (hxi : Function.Injective x) {i j : Fin m} (hij : i < j) : x j - x i ≠ 0 :=
  sub_ne_zero.mpr (fun heq => (ne_of_gt hij) (hxi heq))

theorem energy_vandermonde_product_ne_zero {m : ℕ} (x : Fin m → ℝ)
    (hxi : Function.Injective x) :
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact energy_difference_ne_zero_of_lt x hxi (Finset.mem_Ioi.mp hj)

theorem energy_abs_vandermonde_pos {m : ℕ} (x : Fin m → ℝ)
    (hxi : Function.Injective x) :
    0 < |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)| :=
  abs_pos.mpr (energy_vandermonde_product_ne_zero x hxi)

theorem log_abs_vandermonde {m : ℕ} (x : Fin m → ℝ)
    (hxi : Function.Injective x) :
    Real.log |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)| =
      ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i| := by
  have hrow (i : Fin m) : (∏ j ∈ Finset.Ioi i, (x j - x i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact energy_difference_ne_zero_of_lt x hxi (Finset.mem_Ioi.mp hj)
  simp only [Real.log_abs]
  rw [Real.log_prod (s := Finset.univ)
    (f := fun i : Fin m => ∏ j ∈ Finset.Ioi i, (x j - x i))
    (fun i _ => hrow i)]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.log_prod (s := Finset.Ioi i) (f := fun j => x j - x i)
    (fun j hj => energy_difference_ne_zero_of_lt x hxi (Finset.mem_Ioi.mp hj))

theorem energy_pair_product_pos {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    0 < ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (1 - x i * x j) := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact energy_one_sub_mul_pos (hx i) (hx j)

theorem log_energy_pair_product {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    Real.log (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (1 - x i * x j)) =
      ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j) := by
  have hrow (i : Fin m) : (∏ j ∈ Finset.Ioi i, (1 - x i * x j)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro j _
    exact energy_one_sub_mul_pos (hx i) (hx j)
  rw [Real.log_prod (s := Finset.univ)
    (f := fun i : Fin m => ∏ j ∈ Finset.Ioi i, (1 - x i * x j))
    (fun i _ => hrow i)]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.log_prod (s := Finset.Ioi i) (f := fun j => 1 - x i * x j)
    (fun j _ => (energy_one_sub_mul_pos (hx i) (hx j)).ne')

theorem energy_mixed_product_pos {m : ℕ} (x s : Fin m → ℝ)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    0 < ∏ i : Fin m, ∏ j : Fin m, (1 - 2 * x i * s j + x i ^ 2) := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact realCoordinateInv_kernel_numerator_pos (x i) (hs j)

theorem log_energy_mixed_product {m : ℕ} (x s : Fin m → ℝ)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    Real.log (∏ i : Fin m, ∏ j : Fin m, (1 - 2 * x i * s j + x i ^ 2)) =
      ∑ i : Fin m, ∑ j : Fin m, Real.log (1 - 2 * x i * s j + x i ^ 2) := by
  have hrow (i : Fin m) : (∏ j : Fin m, (1 - 2 * x i * s j + x i ^ 2)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro j _
    exact realCoordinateInv_kernel_numerator_pos (x i) (hs j)
  rw [Real.log_prod (s := Finset.univ)
    (f := fun i : Fin m => ∏ j : Fin m, (1 - 2 * x i * s j + x i ^ 2))
    (fun i _ => hrow i)]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.log_prod (s := Finset.univ) (f := fun j : Fin m => 1 - 2 * x i * s j + x i ^ 2)
    (fun j _ => (realCoordinateInv_kernel_numerator_pos (x i) (hs j)).ne')

theorem energy_s_weight_product_pos (N : ℕ) (s : Fin (n N) → ℝ)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) :
    0 < ∏ i : Fin (n N), (s i ^ b N * (1 - s i) ^ q N) := by
  apply Finset.prod_pos
  intro i _
  exact mul_pos (pow_pos (hs i).1 _) (pow_pos (sub_pos.mpr (hs i).2) _)

theorem energy_node_weight_product_pos (N : ℕ) (k : ℝ) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    0 < ∏ i : Fin (n N),
      (|x i| ^ A N * (1 - x i) ^ (2 * h N) * (1 + x i ^ 2) ^ k) := by
  apply Finset.prod_pos
  intro i _
  exact mul_pos (mul_pos (pow_pos (abs_pos.mpr (hx0 i)) _)
    (pow_pos (sub_pos.mpr (hx i).2) _))
    (Real.rpow_pos_of_pos (realCoordinateInv_denominator_pos (x i)) _)

theorem energy_plain_node_weight_product_pos (N : ℕ) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    0 < ∏ i : Fin (n N), (|x i| ^ A N * (1 - x i) ^ (2 * h N)) := by
  simpa only [Real.rpow_zero, mul_one] using
    energy_node_weight_product_pos N 0 x hx hx0

theorem energy_quadratic_product_pos (N : ℕ) (x : Fin (n N) → ℝ) :
    0 < ∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2) := by
  exact Finset.prod_pos (fun i _ => pow_pos (realCoordinateInv_denominator_pos (x i)) _)

theorem log_energy_s_weight_product (N : ℕ) (s : Fin (n N) → ℝ)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) :
    Real.log (∏ i : Fin (n N), (s i ^ b N * (1 - s i) ^ q N)) =
      ∑ i : Fin (n N), ((b N : ℝ) * Real.log (s i) +
        (q N : ℝ) * Real.log (1 - s i)) := by
  rw [Real.log_prod (fun i _ =>
    mul_ne_zero (pow_ne_zero _ (hs i).1.ne') (pow_ne_zero _ (sub_pos.mpr (hs i).2).ne'))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_mul (pow_ne_zero _ (hs i).1.ne')
    (pow_ne_zero _ (sub_pos.mpr (hs i).2).ne'), Real.log_pow, Real.log_pow]

theorem log_energy_node_weight_product (N : ℕ) (k : ℝ) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    Real.log (∏ i : Fin (n N),
      (|x i| ^ A N * (1 - x i) ^ (2 * h N) * (1 + x i ^ 2) ^ k)) =
      ∑ i : Fin (n N), ((A N : ℝ) * Real.log |x i| +
        ((2 * h N : ℕ) : ℝ) * Real.log (1 - x i) +
        k * Real.log (1 + x i ^ 2)) := by
  have hrow (i : Fin (n N)) :
      0 < |x i| ^ A N * (1 - x i) ^ (2 * h N) * (1 + x i ^ 2) ^ k :=
    mul_pos (mul_pos (pow_pos (abs_pos.mpr (hx0 i)) _)
      (pow_pos (sub_pos.mpr (hx i).2) _))
      (Real.rpow_pos_of_pos (realCoordinateInv_denominator_pos (x i)) _)
  rw [Real.log_prod (fun i _ => (hrow i).ne')]
  apply Finset.sum_congr rfl
  intro i _
  have ha : |x i| ^ A N ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr (hx0 i))
  have hb : (1 - x i) ^ (2 * h N) ≠ 0 := pow_ne_zero _ (sub_pos.mpr (hx i).2).ne'
  have hc : (1 + x i ^ 2) ^ k ≠ 0 :=
    (Real.rpow_pos_of_pos (realCoordinateInv_denominator_pos (x i)) k).ne'
  rw [Real.log_mul (mul_ne_zero ha hb) hc, Real.log_mul ha hb,
    Real.log_pow, Real.log_pow, Real.log_rpow (realCoordinateInv_denominator_pos (x i))]

theorem log_energy_plain_node_weight_product (N : ℕ) (x : Fin (n N) → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    Real.log (∏ i : Fin (n N), (|x i| ^ A N * (1 - x i) ^ (2 * h N))) =
      ∑ i : Fin (n N), ((A N : ℝ) * Real.log |x i| +
        ((2 * h N : ℕ) : ℝ) * Real.log (1 - x i)) := by
  simpa only [Real.rpow_zero, mul_one, zero_mul, add_zero] using
    log_energy_node_weight_product N 0 x hx hx0

theorem log_energy_quadratic_product (N : ℕ) (x : Fin (n N) → ℝ) :
    Real.log (∏ i : Fin (n N), (1 + x i ^ 2) ^ (H N - 2)) =
      ∑ i : Fin (n N), ((H N - 2 : ℕ) : ℝ) * Real.log (1 + x i ^ 2) := by
  rw [Real.log_prod (fun i _ =>
    pow_ne_zero _ (realCoordinateInv_denominator_pos (x i)).ne')]
  simp only [Real.log_pow]

open Set
open scoped BigOperators

theorem log_realEnergyMajorantOne {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (realEnergyMajorantOne N x s) =
      ((n N * (Cdegree N - 1) : ℕ) : ℝ) * Real.log 2 +
      (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) +
      2 * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) +
      (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) +
      (∑ j : Fin (n N), ((b N : ℝ) * Real.log (s j) +
        (q N : ℝ) * Real.log (1 - s j))) +
      (∑ i : Fin (n N), ((A N : ℝ) * Real.log |x i| +
        ((2 * h N : ℕ) : ℝ) * Real.log (1 - x i) +
        (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2) *
          Real.log (1 + x i ^ 2))) -
      (∑ i : Fin (n N), ∑ j : Fin (n N), Real.log (1 - 2 * x i * s j + x i ^ 2)) := by
  have hX := energy_abs_vandermonde_pos x hxi
  have hS := energy_abs_vandermonde_pos s hsi
  have hP := energy_pair_product_pos x hx
  have hK := energy_mixed_product_pos x s hs
  have hSW := energy_s_weight_product_pos N s hs
  have hW := energy_node_weight_product_pos N
    (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2) x hx hx0
  rw [realEnergyMajorantOne_coordinate hN x s hx hx0]
  rw [Real.log_div (by positivity) hK.ne',
    Real.log_mul (by positivity) hW.ne',
    Real.log_mul (by positivity) hSW.ne',
    Real.log_mul (by positivity) hP.ne',
    Real.log_mul (by positivity) (pow_ne_zero _ hS.ne'),
    Real.log_mul (by positivity) hX.ne']
  rw [Real.log_pow, Real.log_pow, log_abs_vandermonde x hxi,
    log_abs_vandermonde s hsi, log_energy_pair_product x hx,
    log_energy_s_weight_product N s hs,
    log_energy_node_weight_product N _ x hx hx0,
    log_energy_mixed_product x s hs]
  norm_num

theorem log_realEnergyMajorantTwo {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (realEnergyMajorantTwo N x s) =
      ((n N * (Cdegree N - 1) + (n N).choose 2 : ℕ) : ℝ) * Real.log 2 +
      2 * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) +
      2 * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) +
      (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) +
      (∑ j : Fin (n N), ((b N : ℝ) * Real.log (s j) +
        (q N : ℝ) * Real.log (1 - s j))) +
      (∑ i : Fin (n N), ((A N : ℝ) * Real.log |x i| +
        ((2 * h N : ℕ) : ℝ) * Real.log (1 - x i) +
        (2 - (Cdegree N : ℝ) - (h N : ℝ)) * Real.log (1 + x i ^ 2))) -
      (∑ i : Fin (n N), ∑ j : Fin (n N), Real.log (1 - 2 * x i * s j + x i ^ 2)) := by
  have hX := energy_abs_vandermonde_pos x hxi
  have hS := energy_abs_vandermonde_pos s hsi
  have hP := energy_pair_product_pos x hx
  have hK := energy_mixed_product_pos x s hs
  have hSW := energy_s_weight_product_pos N s hs
  have hW := energy_plain_node_weight_product_pos N x hx hx0
  have hD := energy_quadratic_product_pos N x
  have hH : 2 ≤ H N := by unfold H; omega
  have hc : ((H N - 2 : ℕ) : ℝ) = (Cdegree N : ℝ) + (h N : ℝ) - 2 := by
    rw [Nat.cast_sub hH, H_eq_Cdegree_add_h, Nat.cast_add, Nat.cast_ofNat]
  rw [realEnergyMajorantTwo_coordinate hN x s hx hx0]
  rw [Real.log_div (by positivity) (mul_pos hK hD).ne',
    Real.log_mul (by positivity) hW.ne',
    Real.log_mul (by positivity) hSW.ne',
    Real.log_mul (by positivity) hP.ne',
    Real.log_mul (by positivity) (pow_ne_zero _ hS.ne'),
    Real.log_mul (by positivity) (pow_ne_zero _ hX.ne'),
    Real.log_mul hK.ne' hD.ne']
  rw [Real.log_pow, Real.log_pow, Real.log_pow,
    log_abs_vandermonde x hxi, log_abs_vandermonde s hsi,
    log_energy_pair_product x hx, log_energy_s_weight_product N s hs,
    log_energy_plain_node_weight_product N x hx hx0,
    log_energy_mixed_product x s hs, log_energy_quadratic_product N x]
  simp only [hc, Nat.cast_ofNat, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.FirstSheetBoundaryMeasure
namespace OAI


noncomputable section

namespace InternalCatalan

open Complex Metric MeasureTheory

/-- Port note (prove2.me): Mathlib 0df444a has no `Mathlib.MeasureTheory.Group.Circle`, which in
newer Mathlib gives the unit circle its Borel σ-algebra; it is supplied here. -/
instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle

instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

def firstSheetAngleMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc 0 (2 * Real.pi))

instance firstSheetAngleMeasure_finite : IsFiniteMeasure firstSheetAngleMeasure := by
  unfold firstSheetAngleMeasure
  apply isFiniteMeasure_restrict.mpr
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

def firstSheetBoundaryScale : NNReal := ⟨(2 * Real.pi)⁻¹, by positivity⟩

def firstSheetBoundaryMeasure : Measure Circle :=
  firstSheetBoundaryScale •
    Measure.map (Circle.exp : ℝ → Circle) firstSheetAngleMeasure

instance firstSheetBoundaryMeasure_finite : IsFiniteMeasure firstSheetBoundaryMeasure := by
  unfold firstSheetBoundaryMeasure
  infer_instance

def firstSheetBoundaryFunction {E : Type*} [TopologicalSpace E]
    (u : ℂ → E) (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) : C(Circle, E) where
  toFun z := u (z : ℂ)
  continuous_toFun := hu.comp_continuous continuous_subtype_val (by
    intro z
    simp only [mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl])

@[simp] theorem firstSheetBoundaryFunction_apply {E : Type*} [TopologicalSpace E]
    (u : ℂ → E) (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) (z : Circle) :
    firstSheetBoundaryFunction u hu z = u (z : ℂ) := rfl

theorem firstSheetBoundary_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] {u : ℂ → E}
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) :
    (∫ z : Circle, u (z : ℂ) ∂firstSheetBoundaryMeasure) =
      Real.circleAverage u 0 1 := by
  have hc : Continuous (fun z : Circle => u (z : ℂ)) :=
    (firstSheetBoundaryFunction u hu).continuous
  unfold firstSheetBoundaryMeasure
  rw [integral_smul_nnreal_measure,
    integral_map_of_stronglyMeasurable Circle.exp.continuous.measurable hc.stronglyMeasurable]
  change (2 * Real.pi)⁻¹ •
      (∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), u (Circle.exp θ : ℂ)) = _
  rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp only [Real.circleAverage_def, Circle.coe_exp, circleMap, ofReal_one,
    one_mul, zero_add]



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.FirstSheetHilbertDeterminant
namespace OAI


noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem firstSheet_det_norm_le_pow {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (L : V →ₗ[ℂ] V) {C : ℝ} (hL : ∀ v, ‖L v‖ ≤ C * ‖v‖) :
    ‖LinearMap.det L‖ ≤ C ^ Module.finrank ℂ V := by
  classical
  let b := stdOrthonormalBasis ℂ V
  let f : Fin (Module.finrank ℂ V) → V := fun i => L (b i)
  have hd : Module.finrank ℂ V = Fintype.card (Fin (Module.finrank ℂ V)) := by simp
  let c := InnerProductSpace.gramSchmidtOrthonormalBasis hd f
  have hdet : ‖c.toBasis.det f‖ = ‖LinearMap.det L‖ := by
    change ‖c.toBasis.det (L ∘ b)‖ = _
    rw [Module.Basis.det_comp, norm_mul,
      OrthonormalBasis.det_to_matrix_orthonormalBasis, mul_one]
  have hprod : ‖c.toBasis.det f‖ =
      ∏ i, ‖inner ℂ (c i) (f i)‖ := by
    simpa only [norm_prod] using congrArg (fun z : ℂ => ‖z‖)
      (InnerProductSpace.gramSchmidtOrthonormalBasis_det hd f)
  calc
    ‖LinearMap.det L‖ = ∏ i, ‖inner ℂ (c i) (f i)‖ := hdet.symm.trans hprod
    _ ≤ ∏ _i : Fin (Module.finrank ℂ V), C := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro i _
      calc
        ‖inner ℂ (c i) (f i)‖ ≤ ‖c i‖ * ‖f i‖ := norm_inner_le_norm _ _
        _ = ‖L (b i)‖ := by simp only [c.norm_eq_one, one_mul, f]
        _ ≤ C := by simpa only [b.norm_eq_one, mul_one] using hL (b i)
    _ = C ^ Module.finrank ℂ V := by simp

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.FirstSheetReproducingKernel
namespace OAI


noncomputable section

namespace InternalCatalan

open Complex Metric
open scoped ComplexConjugate

def firstSheetKernel (x : ℝ) (z : ℂ) : ℂ := (1 - (x : ℂ) * z)⁻¹

theorem firstSheetKernel_denominator_ne_zero {x : ℝ} {z : ℂ}
    (hx : |x| < 1) (hz : ‖z‖ ≤ 1) : 1 - (x : ℂ) * z ≠ 0 := by
  have hm : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |x| * ‖z‖ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hz (abs_nonneg x)
      _ < 1 := by simpa only [mul_one] using hx
  intro h
  have heq : (x : ℂ) * z = 1 := (sub_eq_zero.mp h).symm
  rw [heq, norm_one] at hm
  exact (lt_irrefl 1) hm

theorem conj_firstSheetKernel_on_circle (x : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    conj (firstSheetKernel x z) = z / (z - (x : ℂ)) := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have heq : (1 : ℂ) - (x : ℂ) * z⁻¹ = (z - (x : ℂ)) / z := by
    field_simp [hz0]
  simp only [firstSheetKernel, map_inv₀, map_sub, map_one, map_mul,
    Complex.conj_ofReal, ← Complex.inv_eq_conj hz]
  rw [heq]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]

theorem firstSheetKernel_continuousOn_closedDisk {x : ℝ} (hx : |x| < 1) :
    ContinuousOn (firstSheetKernel x) (closedBall (0 : ℂ) 1) := by
  change ContinuousOn (fun z : ℂ => (1 - (x : ℂ) * z)⁻¹) (closedBall (0 : ℂ) 1)
  have hc : Continuous (fun z : ℂ => 1 - (x : ℂ) * z) := by fun_prop
  apply hc.continuousOn.inv₀
  intro z hz
  apply firstSheetKernel_denominator_ne_zero hx
  simpa only [mem_closedBall, dist_zero_right] using hz


theorem circleAverage_mul_conj_firstSheetKernel {u : ℂ → ℂ}
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) 1)) {x : ℝ} (hx : |x| < 1) :
    Real.circleAverage (fun z => u z * conj (firstSheetKernel x z)) 0 1 = u x := by
  have hd : DiffContOnCl ℂ u (ball (0 : ℂ) 1) :=
    hu.differentiableOn.diffContOnCl_ball Set.Subset.rfl
  have hxball : (x : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hx
  rw [Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  have hint :
      (∮ z in C((0 : ℂ), 1), (z - 0)⁻¹ • (u z * conj (firstSheetKernel x z))) =
      ∮ z in C((0 : ℂ), 1), (z - (x : ℂ))⁻¹ • u z := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := by
      intro h
      simp [h] at hzn
    simp only [sub_zero, smul_eq_mul, conj_firstSheetKernel_on_circle x hzn,
      div_eq_mul_inv]
    calc
      z⁻¹ * (u z * (z * (z - (x : ℂ))⁻¹)) =
          (z⁻¹ * z) * ((z - (x : ℂ))⁻¹ * u z) := by ring
      _ = (z - (x : ℂ))⁻¹ * u z := by rw [inv_mul_cancel₀ hz0, one_mul]
  rw [hint]
  exact hd.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hxball


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.RealSheetIntegralBound
namespace OAI


noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace InternalCatalan

private theorem pair_product_eq_zero_of_not_injective {m : ℕ}
    (v : Fin m → ℝ) (hv : ¬Function.Injective v) :
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (v j - v i)) = 0 := by
  have hd : (Matrix.vandermonde v).det = 0 := by
    by_contra hd
    exact hv (Matrix.det_vandermonde_ne_zero_iff.mp hd)
  simpa only [Matrix.det_vandermonde] using hd

theorem sheetRealIntegrand_eq_zero_of_not_injective_x (N : ℕ)
    (x s : Fin (n N) → ℝ) (hx : ¬Function.Injective x) :
    sheetRealIntegrand N x s = 0 := by
  have hcomp : ¬Function.Injective (fun i => realCoordinateInv (x i)) := by
    intro h
    apply hx
    intro i j hij
    exact h (congrArg realCoordinateInv hij)
  have hz := pair_product_eq_zero_of_not_injective
    (fun i => realCoordinateInv (x i)) hcomp
  simp only [sheetRealIntegrand, hz, mul_zero, zero_mul, zero_div]

theorem sheetRealIntegrand_eq_zero_of_not_injective_s (N : ℕ)
    (x s : Fin (n N) → ℝ) (hs : ¬Function.Injective s) :
    sheetRealIntegrand N x s = 0 := by
  have hz := pair_product_eq_zero_of_not_injective s hs
  simp only [sheetRealIntegrand, hz, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_mul, zero_div]

theorem ae_realCoordinate_pair_domain (N : ℕ) :
    ∀ᵐ p ∂realCoordinateListPairMeasure N,
      (∀ i, p.1 i ∈ Ioo (-1 : ℝ) 1 ∧ p.1 i ≠ 0) ∧
        (∀ j, p.2 j ∈ Ioo (0 : ℝ) 1) := by
  have hx : ∀ᵐ p ∂realCoordinateListPairMeasure N,
      ∀ i, p.1 i ∈ Ioo (-1 : ℝ) 1 ∧ p.1 i ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure))
      (ν := Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))).tendsto_ae.eventually
        (ae_realCoordinate_list_regular N)
  have hslist : ∀ᵐ s ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)),
      ∀ j, s j ∈ Ioo (0 : ℝ) 1 :=
    Filter.eventually_all.2 (fun j =>
      (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)) (i := j)).eventually
          (ae_restrict_mem measurableSet_Ioo))
  have hs : ∀ᵐ p ∂realCoordinateListPairMeasure N,
      ∀ j, p.2 j ∈ Ioo (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_snd
      (μ := Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure))
      (ν := Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))).tendsto_ae.eventually
        hslist
  exact hx.and hs

theorem realCoordinateListPairMeasure_univ (N : ℕ) :
    realCoordinateListPairMeasure N univ = (2 : ℝ≥0∞) ^ n N := by
  unfold realCoordinateListPairMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod]
  simp [Measure.pi_univ, realCoordinateMeasure_univ]

theorem realCoordinateListPairMeasure_real_univ (N : ℕ) :
    (realCoordinateListPairMeasure N).real univ = (2 : ℝ) ^ n N := by
  rw [measureReal_def, realCoordinateListPairMeasure_univ, ENNReal.toReal_pow]
  norm_num

theorem ae_abs_sheetRealIntegrand_le_of_regular_bound (N : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hbound : ∀ (x s : Fin (n N) → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      |sheetRealIntegrand N x s| ≤ B) :
    ∀ᵐ p ∂realCoordinateListPairMeasure N, |sheetRealIntegrand N p.1 p.2| ≤ B := by
  filter_upwards [ae_realCoordinate_pair_domain N] with p hp
  by_cases hxi : Function.Injective p.1
  · by_cases hsi : Function.Injective p.2
    · exact hbound p.1 p.2 (fun i => (hp.1 i).1) hp.2 (fun i => (hp.1 i).2) hxi hsi
    · rw [sheetRealIntegrand_eq_zero_of_not_injective_s N p.1 p.2 hsi, abs_zero]
      exact hB
  · rw [sheetRealIntegrand_eq_zero_of_not_injective_x N p.1 p.2 hxi, abs_zero]
    exact hB

theorem determinant_eq_sheetRealPairIntegral {N : ℕ} (hN : 0 < N) :
    determinant N = 1 / (((n N).factorial : ℝ) ^ 2) *
      ∫ p, sheetRealIntegrand N p.1 p.2 ∂realCoordinateListPairMeasure N := by
  rw [determinant_eq_sheetRealIntegral hN]
  congr 1
  exact (integral_prod _ (integrable_sheetRealIntegrand hN)).symm

theorem abs_determinant_le_of_sheetRealIntegrand_bound {N : ℕ} (hN : 0 < N)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ (x s : Fin (n N) → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      |sheetRealIntegrand N x s| ≤ B) :
    |determinant N| ≤
      ((2 : ℝ) ^ n N / (((n N).factorial : ℝ) ^ 2)) * B := by
  let : IsFiniteMeasure (realCoordinateListPairMeasure N) := by
    unfold realCoordinateListPairMeasure
    infer_instance
  have hae := ae_abs_sheetRealIntegrand_le_of_regular_bound N hB hbound
  have hnorm : ∀ᵐ p ∂realCoordinateListPairMeasure N,
      ‖sheetRealIntegrand N p.1 p.2‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using hae
  have hint : |∫ p, sheetRealIntegrand N p.1 p.2 ∂realCoordinateListPairMeasure N| ≤
      B * (2 : ℝ) ^ n N := by
    simpa only [Real.norm_eq_abs, realCoordinateListPairMeasure_real_univ] using
      norm_integral_le_of_norm_le_const hnorm
  have hfactor : 0 ≤ 1 / (((n N).factorial : ℝ) ^ 2) := by positivity
  rw [determinant_eq_sheetRealPairIntegral hN, abs_mul, abs_of_nonneg hfactor]
  calc
    _ ≤ (1 / (((n N).factorial : ℝ) ^ 2)) * (B * (2 : ℝ) ^ n N) :=
      mul_le_mul_of_nonneg_left hint hfactor
    _ = _ := by ring


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.BlaschkeUniformInterpolation
namespace OAI


noncomputable section
namespace InternalCatalan

theorem imaginary_path_dist (t u : ℝ) :
    ‖Complex.I * (t : ℂ) - Complex.I * (u : ℂ)‖ = |t - u| := by
  rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

theorem upper_circle_crossing_location {r : ℝ} {z : ℂ}
    (hz : ‖z‖ = 1) (him : 0 ≤ z.im) (hre : |z.re| ≤ r / 10) :
    1 - r / 10 ≤ z.im ∧ z.im ≤ 1 ∧ ‖z - Complex.I‖ ≤ r / 5 := by
  have himhi : z.im ≤ 1 := by
    calc
      z.im ≤ |z.im| := le_abs_self _
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
      _ = 1 := hz
  have hl := Complex.norm_le_abs_re_add_abs_im z
  rw [hz, abs_of_nonneg him] at hl
  refine ⟨by linarith, himhi, ?_⟩
  have hn := Complex.norm_le_abs_re_add_abs_im (z - Complex.I)
  simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im] at hn
  rw [abs_of_nonpos (sub_nonpos.mpr himhi)] at hn
  linarith

theorem upper_crossing_far_separation {r t : ℝ} {z : ℂ} (hr : 0 ≤ r)
    (hz : 1 - r / 10 ≤ z.im) (ht : t ≤ 1 - r) :
    r / 2 ≤ ‖Complex.I * (t : ℂ) - z‖ := by
  have hv := Complex.abs_im_le_norm (Complex.I * (t : ℂ) - z)
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] at hv
  have ha := neg_le_abs (t - z.im)
  linarith

theorem upper_crossing_local_path {r t : ℝ} (hr : 0 ≤ r)
    (htl : 1 - r ≤ t) (htu : t ≤ 1 + 2 * r) :
    ‖Complex.I * (t : ℂ) - Complex.I‖ ≤ 2 * r := by
  have hnorm : ‖Complex.I * (t : ℂ) - Complex.I‖ = |t - 1| := by
    simpa only [Complex.ofReal_one, mul_one] using imaginary_path_dist t 1
  rw [hnorm]
  apply abs_le.mpr
  constructor <;> linarith

theorem upper_crossing_endpoint_distances {r : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hrsmall : r ≤ (1 / 48 : ℝ))
    (hz : ‖z‖ = 1) (him : 0 ≤ z.im) (hre : |z.re| ≤ r / 10) :
    (r / 2 ≤ ‖Complex.I * ((1 - r : ℝ) : ℂ) - z‖ ∧
      ‖Complex.I * ((1 - r : ℝ) : ℂ) - z‖ ≤ 1) ∧
    (r / 2 ≤ ‖Complex.I * ((1 + 2 * r : ℝ) : ℂ) - z‖ ∧
      ‖Complex.I * ((1 + 2 * r : ℝ) : ℂ) - z‖ ≤ 1) := by
  have hloc := upper_circle_crossing_location hz him hre
  have hu (t : ℝ) (htl : 1 - r ≤ t) (htu : t ≤ 1 + 2 * r) :
      ‖Complex.I * (t : ℂ) - z‖ ≤ 1 := by
    have htri := norm_add_le (Complex.I * (t : ℂ) - Complex.I) (Complex.I - z)
    have heq : (Complex.I * (t : ℂ) - Complex.I) + (Complex.I - z) =
        Complex.I * (t : ℂ) - z := by ring
    rw [heq, norm_sub_rev Complex.I z] at htri
    have hp := upper_crossing_local_path hr htl htu
    linarith [hloc.2.2]
  refine ⟨⟨upper_crossing_far_separation hr hloc.1 le_rfl, hu _ le_rfl (by linarith)⟩,
    ⟨?_, hu _ (by linarith) le_rfl⟩⟩
  have hv := Complex.abs_im_le_norm (Complex.I * ((1 + 2 * r : ℝ) : ℂ) - z)
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] at hv
  have ha := le_abs_self (1 + 2 * r - z.im)
  linarith [hloc.2.1]

theorem imaginary_path_neg_distance (t : ℝ) (z : ℂ) :
    ‖Complex.I * ((-t : ℝ) : ℂ) - (-z)‖ = ‖Complex.I * (t : ℂ) - z‖ := by
  have heq : Complex.I * ((-t : ℝ) : ℂ) - (-z) = -(Complex.I * (t : ℂ) - z) := by
    simp only [Complex.ofReal_neg]
    ring
  rw [heq, norm_neg]

theorem lower_circle_crossing_location {r : ℝ} {z : ℂ}
    (hz : ‖z‖ = 1) (him : z.im ≤ 0) (hre : |z.re| ≤ r / 10) :
    -1 ≤ z.im ∧ z.im ≤ -1 + r / 10 ∧ ‖z + Complex.I‖ ≤ r / 5 := by
  have hh := upper_circle_crossing_location (z := -z)
    (by simpa only [norm_neg] using hz)
    (by simpa only [Complex.neg_im] using neg_nonneg.mpr him)
    (by simpa only [Complex.neg_re, abs_neg] using hre)
  have heq : -z - Complex.I = -(z + Complex.I) := by ring
  rw [heq, norm_neg] at hh
  simp only [Complex.neg_im] at hh
  exact ⟨by linarith [hh.2.1], by linarith [hh.1], hh.2.2⟩

theorem lower_crossing_far_separation {r t : ℝ} {z : ℂ} (hr : 0 ≤ r)
    (hz : z.im ≤ -1 + r / 10) (ht : -1 + r ≤ t) :
    r / 2 ≤ ‖Complex.I * (t : ℂ) - z‖ := by
  have hh := upper_crossing_far_separation (z := -z) (t := -t) hr
    (by simp only [Complex.neg_im]; linarith) (by linarith)
  rwa [imaginary_path_neg_distance] at hh

theorem lower_crossing_local_path {r t : ℝ} (hr : 0 ≤ r)
    (htl : -1 - 2 * r ≤ t) (htu : t ≤ -1 + r) :
    ‖Complex.I * (t : ℂ) + Complex.I‖ ≤ 2 * r := by
  have hh := upper_crossing_local_path (t := -t) hr (by linarith) (by linarith)
  have heq : Complex.I * ((-t : ℝ) : ℂ) - Complex.I =
      -(Complex.I * (t : ℂ) + Complex.I) := by simp only [Complex.ofReal_neg]; ring
  rwa [heq, norm_neg] at hh

theorem lower_crossing_endpoint_distances {r : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hrsmall : r ≤ (1 / 48 : ℝ))
    (hz : ‖z‖ = 1) (him : z.im ≤ 0) (hre : |z.re| ≤ r / 10) :
    (r / 2 ≤ ‖Complex.I * ((-1 - 2 * r : ℝ) : ℂ) - z‖ ∧
      ‖Complex.I * ((-1 - 2 * r : ℝ) : ℂ) - z‖ ≤ 1) ∧
    (r / 2 ≤ ‖Complex.I * ((-1 + r : ℝ) : ℂ) - z‖ ∧
      ‖Complex.I * ((-1 + r : ℝ) : ℂ) - z‖ ≤ 1) := by
  have hh := upper_crossing_endpoint_distances hr hrsmall (z := -z)
    (by simpa only [norm_neg] using hz)
    (by simpa only [Complex.neg_im] using neg_nonneg.mpr him)
    (by simpa only [Complex.neg_re, abs_neg] using hre)
  have heq1 : (1 - r : ℝ) = -(-1 + r) := by ring
  have heq2 : (1 + 2 * r : ℝ) = -(-1 - 2 * r) := by ring
  rw [heq1, heq2, imaginary_path_neg_distance, imaginary_path_neg_distance] at hh
  exact ⟨hh.2, hh.1⟩






def circleRightPerturb (z : ℂ) (t : ℝ) : ℂ :=
  (z + (t : ℂ)) / (‖z + (t : ℂ)‖ : ℂ)

theorem circleRightPerturb_zero {z : ℂ} (hz : ‖z‖ = 1) : circleRightPerturb z 0 = z := by
  simp [circleRightPerturb, hz]

theorem circleRightPerturb_continuousAt_zero {z : ℂ} (hz : ‖z‖ = 1) :
    ContinuousAt (circleRightPerturb z) 0 := by
  have hn : Continuous (fun t : ℝ => z + (t : ℂ)) := continuous_const.add Complex.continuous_ofReal
  have hd : Continuous (fun t : ℝ => (‖z + (t : ℂ)‖ : ℂ)) :=
    Complex.continuous_ofReal.comp hn.norm
  have hd0 : (‖z + ((0 : ℝ) : ℂ)‖ : ℂ) ≠ 0 := by simp [hz]
  exact hn.continuousAt.div hd.continuousAt hd0

theorem circleRightPerturb_norm_and_re {z : ℂ} (hz : z.re = 0) {t : ℝ} (ht : 0 < t) :
    ‖circleRightPerturb z t‖ = 1 ∧ (circleRightPerturb z t).re ≠ 0 := by
  have hv : z + (t : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re, hz, zero_add] at hr
    exact ht.ne' hr
  have hn : ‖z + (t : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnc : (‖z + (t : ℂ)‖ : ℂ) ≠ 0 := by
    intro h
    exact hn (by simpa only [Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re h)
  constructor
  · unfold circleRightPerturb
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self hn]
  · intro hzero
    have hm : circleRightPerturb z t * (‖z + (t : ℂ)‖ : ℂ) = z + (t : ℂ) :=
      div_mul_cancel₀ _ hnc
    have hr := congrArg Complex.re hm
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, Complex.add_re, hz, hzero, zero_mul, zero_add] at hr
    exact ht.ne' hr.symm

end InternalCatalan




open Polynomial
open scoped BigOperators
namespace InternalCatalan

def polynomialDividedDifference (p : ℂ[X]) (z w : ℂ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * ∑ j ∈ Finset.range k, z ^ j * w ^ (k - 1 - j)

theorem sub_mul_polynomialDividedDifference (p : ℂ[X]) (z w : ℂ) :
    (w - z) * polynomialDividedDifference p z w = p.eval w - p.eval z := by
  unfold polynomialDividedDifference
  rw [Finset.mul_sum, eval_eq_sum, eval_eq_sum, sum_def, sum_def,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (w - z) * (p.coeff k * ∑ j ∈ Finset.range k, z ^ j * w ^ (k - 1 - j)) =
        p.coeff k * ((w - z) * ∑ j ∈ Finset.range k, z ^ j * w ^ (k - 1 - j)) := by ring
    _ = p.coeff k * (w ^ k - z ^ k) := by rw [(Commute.all z w).mul_neg_geom_sum₂ k]
    _ = p.coeff k * w ^ k - p.coeff k * z ^ k := by ring


theorem polynomialDividedDifference_analyticAt_right (p : ℂ[X]) (z w : ℂ) :
    AnalyticAt ℂ (fun v => polynomialDividedDifference p z v) w := by
  unfold polynomialDividedDifference
  apply Finset.analyticAt_fun_sum
  intro k _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro j _
  exact analyticAt_const.mul (analyticAt_id.pow (k - 1 - j))

theorem polynomialEval_analyticAt (p : ℂ[X]) (z : ℂ) :
    AnalyticAt ℂ (fun v => p.eval v) z := by
  simp only [eval_eq_sum, sum_def]
  apply Finset.analyticAt_fun_sum
  intro k _
  exact analyticAt_const.mul (analyticAt_id.pow k)

def blaschkeDensityRemainder {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (z w : ℂ) : ℂ :=
  (polynomialDividedDifference (blaschkeDensityNumerator s x D) z w *
      (blaschkeNodePolynomial s x).eval z -
    (blaschkeDensityNumerator s x D).eval z *
      polynomialDividedDifference (blaschkeNodePolynomial s x) z w) /
    ((blaschkeNodePolynomial s x).eval w * (blaschkeNodePolynomial s x).eval z)

theorem blaschkeDensity_eq_add_remainder {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) {z w : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0)
    (hw : (blaschkeNodePolynomial s x).eval w ≠ 0) :
    blaschkeDensity s x D w = blaschkeDensity s x D z +
      (w - z) * blaschkeDensityRemainder s x D z w := by
  let A := blaschkeDensityNumerator s x D
  let P := blaschkeNodePolynomial s x
  have hnum : (w - z) *
      (polynomialDividedDifference A z w * P.eval z -
        A.eval z * polynomialDividedDifference P z w) =
      A.eval w * P.eval z - A.eval z * P.eval w := by
    calc
      _ = ((w - z) * polynomialDividedDifference A z w) * P.eval z -
          A.eval z * ((w - z) * polynomialDividedDifference P z w) := by ring
      _ = _ := by rw [sub_mul_polynomialDividedDifference,
                       sub_mul_polynomialDividedDifference]; ring
  rw [blaschkeDensity_eq_eval_div, blaschkeDensity_eq_eval_div]
  change A.eval w / P.eval w = A.eval z / P.eval z + (w - z) *
    ((polynomialDividedDifference A z w * P.eval z -
      A.eval z * polynomialDividedDifference P z w) / (P.eval w * P.eval z))
  rw [← mul_div_assoc, hnum]
  field_simp [show P.eval z ≠ 0 from hz, show P.eval w ≠ 0 from hw]
  ring



end InternalCatalan

end



noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators Interval
namespace InternalCatalan

def blaschkeCauchyMoment {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T : ℝ) (k : ℕ) : ℂ :=
  ∫ t in -T..T, (Complex.I * (t : ℂ)) ^ k /
    (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))

def blaschkeIntegratedDividedDifference {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T : ℝ) (p : ℂ[X]) (z : ℂ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * ∑ j ∈ Finset.range k,
    z ^ j * blaschkeCauchyMoment s x T (k - 1 - j)

private theorem continuous_nodePolynomial_imaginary {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) :
    Continuous (fun t : ℝ => (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) := by
  have hp : Continuous (fun z : ℂ => (blaschkeNodePolynomial s x).eval z) :=
    continuous_iff_continuousAt.mpr (fun z => (polynomialEval_analyticAt _ z).continuousAt)
  exact hp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem continuous_blaschkeCauchyMoment_integrand {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0) (k : ℕ) :
    Continuous (fun t : ℝ => (Complex.I * (t : ℂ)) ^ k /
      (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) := by
  exact ((continuous_const.mul Complex.continuous_ofReal).pow k).div
    (continuous_nodePolynomial_imaginary s x)
    (blaschkeNodePolynomial_eval_imaginary_ne_zero s x hx)

theorem intervalIntegrable_blaschkeCauchyMoment_integrand {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0) (T : ℝ) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => (Complex.I * (t : ℂ)) ^ k /
      (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) volume (-T) T :=
  (continuous_blaschkeCauchyMoment_integrand s x hx k).intervalIntegrable _ _

theorem intervalIntegrable_blaschkeDividedDifference_quotient {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0)
    (T : ℝ) (p : ℂ[X]) (z : ℂ) :
    IntervalIntegrable (fun t : ℝ =>
      polynomialDividedDifference p z (Complex.I * (t : ℂ)) /
        (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) volume (-T) T := by
  have hdd : Continuous (fun w : ℂ => polynomialDividedDifference p z w) :=
    continuous_iff_continuousAt.mpr
      (fun w => (polynomialDividedDifference_analyticAt_right p z w).continuousAt)
  have hpath : Continuous (fun t : ℝ => Complex.I * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have hc : Continuous (fun t : ℝ =>
      polynomialDividedDifference p z (Complex.I * (t : ℂ)) /
        (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) :=
    (hdd.comp hpath).div
    (continuous_nodePolynomial_imaginary s x)
    (blaschkeNodePolynomial_eval_imaginary_ne_zero s x hx)
  exact hc.intervalIntegrable _ _

theorem integral_blaschkeDividedDifference_quotient {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0)
    (T : ℝ) (p : ℂ[X]) (z : ℂ) :
    (∫ t in -T..T, polynomialDividedDifference p z (Complex.I * (t : ℂ)) /
      (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) =
      blaschkeIntegratedDividedDifference s x T p z := by
  have hterm (k j : ℕ) : IntervalIntegrable (fun t : ℝ => z ^ j *
      ((Complex.I * (t : ℂ)) ^ (k - 1 - j) /
        (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ)))) volume (-T) T :=
    (intervalIntegrable_blaschkeCauchyMoment_integrand s x hx T (k - 1 - j)).const_mul _
  have hsum (k : ℕ) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ Finset.range k,
      z ^ j * ((Complex.I * (t : ℂ)) ^ (k - 1 - j) /
        (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ)))) volume (-T) T := by
    convert! IntervalIntegrable.sum (Finset.range k) (fun j _ => hterm k j) using 1
    funext t
    simp only [Finset.sum_apply]
  simp only [polynomialDividedDifference, blaschkeIntegratedDividedDifference,
    Finset.sum_div, mul_div_assoc]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (hsum k).const_mul (p.coeff k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun j _ => hterm k j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem blaschkeIntegratedDividedDifference_analyticAt {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (T : ℝ) (p : ℂ[X]) (z : ℂ) :
    AnalyticAt ℂ (blaschkeIntegratedDividedDifference s x T p) z := by
  unfold blaschkeIntegratedDividedDifference
  apply Finset.analyticAt_fun_sum
  intro k _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (analyticAt_id.pow j).mul analyticAt_const

end InternalCatalan

end



noncomputable section
open MeasureTheory Polynomial
open scoped Interval
namespace InternalCatalan

def blaschkeCauchyRemainder {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  blaschkeIntegratedDividedDifference s x T (blaschkeDensityNumerator s x D) z -
    ((blaschkeDensityNumerator s x D).eval z / (blaschkeNodePolynomial s x).eval z) *
      blaschkeIntegratedDividedDifference s x T (blaschkeNodePolynomial s x) z

theorem blaschkeDensityRemainder_eq_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) {z w : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0)
    (hw : (blaschkeNodePolynomial s x).eval w ≠ 0) :
    blaschkeDensityRemainder s x D z w =
      polynomialDividedDifference (blaschkeDensityNumerator s x D) z w /
        (blaschkeNodePolynomial s x).eval w -
      ((blaschkeDensityNumerator s x D).eval z / (blaschkeNodePolynomial s x).eval z) *
        (polynomialDividedDifference (blaschkeNodePolynomial s x) z w /
          (blaschkeNodePolynomial s x).eval w) := by
  unfold blaschkeDensityRemainder
  field_simp [hz, hw]

private theorem remainder_path_eq {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) :
    (fun t : ℝ => blaschkeDensityRemainder s x D z (Complex.I * (t : ℂ))) =
      (fun t : ℝ =>
        polynomialDividedDifference (blaschkeDensityNumerator s x D) z (Complex.I * (t : ℂ)) /
          (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ)) -
        ((blaschkeDensityNumerator s x D).eval z / (blaschkeNodePolynomial s x).eval z) *
          (polynomialDividedDifference (blaschkeNodePolynomial s x) z (Complex.I * (t : ℂ)) /
            (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ)))) := by
  funext t
  exact blaschkeDensityRemainder_eq_sub s x D hz
    (blaschkeNodePolynomial_eval_imaginary_ne_zero s x hx t)

theorem intervalIntegrable_blaschkeDensityRemainder {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D : ℕ) (T : ℝ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) :
    IntervalIntegrable (fun t : ℝ => blaschkeDensityRemainder s x D z (Complex.I * (t : ℂ)))
      volume (-T) T := by
  rw [remainder_path_eq s x D hx hz]
  exact (intervalIntegrable_blaschkeDividedDifference_quotient s x hx T _ z).sub
    ((intervalIntegrable_blaschkeDividedDifference_quotient s x hx T _ z).const_mul _)

theorem integral_blaschkeDensityRemainder {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D : ℕ) (T : ℝ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) :
    (∫ t in -T..T, blaschkeDensityRemainder s x D z (Complex.I * (t : ℂ))) =
      blaschkeCauchyRemainder s x D T z := by
  rw [remainder_path_eq s x D hx hz]
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_blaschkeDividedDifference_quotient s x hx T _ z)
    ((intervalIntegrable_blaschkeDividedDifference_quotient s x hx T _ z).const_mul _),
    intervalIntegral.integral_const_mul,
    integral_blaschkeDividedDifference_quotient s x hx,
    integral_blaschkeDividedDifference_quotient s x hx]
  rfl


theorem integral_blaschkeCauchyKernel_eq_scalar_add_remainder {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D : ℕ) (T : ℝ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) (hre : z.re ≠ 0) :
    (∫ t in -T..T, blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)) =
      blaschkeDensity s x D z *
        (∫ t in -T..T, (1 : ℂ) / (Complex.I * (t : ℂ) - z)) +
      blaschkeCauchyRemainder s x D T z := by
  have hfun : (fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)) =
      (fun t : ℝ => blaschkeDensity s x D z * (1 / (Complex.I * (t : ℂ) - z)) +
        blaschkeDensityRemainder s x D z (Complex.I * (t : ℂ))) := by
    funext t
    rw [blaschkeDensity_eq_add_remainder s x D hz
      (blaschkeNodePolynomial_eval_imaginary_ne_zero s x hx t)]
    field_simp [imaginary_sub_ne_zero_of_re_ne_zero hre t]
  rw [hfun, intervalIntegral.integral_add
    ((intervalIntegrable_cauchyConstantKernel T hre).const_mul _)
    (intervalIntegrable_blaschkeDensityRemainder s x D T hx hz),
    intervalIntegral.integral_const_mul, integral_blaschkeDensityRemainder s x D T hx hz]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

private theorem complexLog_analyticAt {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    AnalyticAt ℂ Complex.log w := by
  have hd : DifferentiableOn ℂ Complex.log Complex.slitPlane :=
    fun z hz => (Complex.differentiableAt_log hz).differentiableWithinAt
  exact hd.analyticOnNhd Complex.isOpen_slitPlane w hw

theorem cauchyLogLeft_analyticAt {T : ℝ} {z : ℂ} (hlo : -T < z.im) (hhi : z.im < T) :
    AnalyticAt ℂ (cauchyLogLeft T) z := by
  have ha : Complex.I * (T : ℂ) - z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa [Complex.mul_im] using (sub_pos.mpr hhi).ne'
  have hb : -Complex.I * (T : ℂ) - z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    have hn : -T - z.im < 0 := by linarith
    simpa [Complex.mul_im] using hn.ne
  have hfa : AnalyticAt ℂ (fun v : ℂ => Complex.I * (T : ℂ) - v) z :=
    analyticAt_const.sub analyticAt_id
  have hfb : AnalyticAt ℂ (fun v : ℂ => -Complex.I * (T : ℂ) - v) z :=
    analyticAt_const.sub analyticAt_id
  unfold cauchyLogLeft
  exact analyticAt_const.mul
    (((complexLog_analyticAt ha).comp hfa).sub ((complexLog_analyticAt hb).comp hfb))


theorem blaschkeDensity_analyticAt_of_nodePolynomial_ne_zero {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D : ℕ) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) :
    AnalyticAt ℂ (blaschkeDensity s x D) z := by
  have hfun : blaschkeDensity s x D = fun v =>
      (blaschkeDensityNumerator s x D).eval v / (blaschkeNodePolynomial s x).eval v :=
    funext (blaschkeDensity_eq_eval_div s x D)
  rw [hfun]
  exact (polynomialEval_analyticAt _ _).div (polynomialEval_analyticAt _ _) hz

def blaschkeCauchyLeft {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (z : ℂ) : ℂ :=
  ((3 / Real.pi : ℝ) : ℂ) *
    (blaschkeDensity s x D z * cauchyLogLeft (1 + 2 / (n : ℝ)) z +
      blaschkeCauchyRemainder s x D (1 + 2 / (n : ℝ)) z)

def blaschkeCauchyRight {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (z : ℂ) : ℂ :=
  ((3 / Real.pi : ℝ) : ℂ) *
    (blaschkeDensity s x D z * cauchyLogRight (1 + 2 / (n : ℝ)) z +
      blaschkeCauchyRemainder s x D (1 + 2 / (n : ℝ)) z)

theorem blaschkeCauchyTransform_eq_left {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) (hre : z.re < 0) :
    blaschkeCauchyTransform s x D n z = blaschkeCauchyLeft s x D n z := by
  rw [blaschkeCauchyTransform_normalized,
    integral_blaschkeCauchyKernel_eq_scalar_add_remainder s x D _ hx hz hre.ne,
    integral_cauchyConstantKernel_eq_left _ hre]
  rfl

theorem blaschkeCauchyTransform_eq_right {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) (hre : 0 < z.re) :
    blaschkeCauchyTransform s x D n z = blaschkeCauchyRight s x D n z := by
  rw [blaschkeCauchyTransform_normalized,
    integral_blaschkeCauchyKernel_eq_scalar_add_remainder s x D _ hx hz hre.ne',
    integral_cauchyConstantKernel_eq_right _ hre]
  rfl



theorem blaschkeCauchyLeft_sub_right {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) {z : ℂ}
    (hlo : -(1 + 2 / (n : ℝ)) < z.im) (hhi : z.im < 1 + 2 / (n : ℝ)) :
    blaschkeCauchyLeft s x D n z - blaschkeCauchyRight s x D n z =
      6 * blaschkeDensity s x D z := by
  have hp : (Real.pi : ℂ) ≠ 0 := by
    intro h
    exact Real.pi_pos.ne' (by simpa using congrArg Complex.re h)
  have hcoeff : ((3 / Real.pi : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 6 := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    field_simp [hp]
    ring
  unfold blaschkeCauchyLeft blaschkeCauchyRight
  calc
    _ = (((3 / Real.pi : ℝ) : ℂ) *
        (cauchyLogLeft (1 + 2 / (n : ℝ)) z - cauchyLogRight (1 + 2 / (n : ℝ)) z)) *
        blaschkeDensity s x D z := by ring
    _ = _ := by rw [cauchyLogLeft_sub_cauchyLogRight hlo hhi, hcoeff]

end InternalCatalan

end



noncomputable section
namespace InternalCatalan

theorem blaschkeDensity_endpoint_difference_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx : ∀ i ∈ s, |x i| < 1)
    {c z w : ℂ} (hc : ‖c‖ = 1) (hci : |c.im| = 1)
    (hz : ‖z - c‖ ≤ 3 / (n : ℝ)) (hw : ‖w - c‖ ≤ 3 / (n : ℝ)) :
    ‖blaschkeDensity s x D w - blaschkeDensity s x D z‖ ≤
      (4 * (n : ℝ) * Real.exp 12) * ‖w - z‖ := by
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hquarter : 3 / (n : ℝ) ≤ (1 / 4 : ℝ) := (div_le_iff₀ hnpos).mpr (by linarith)
  have hd : ∀ u ∈ Metric.closedBall c (3 / (n : ℝ)),
      DifferentiableAt ℂ (blaschkeDensity s x D) u := by
    intro u hu
    have hu' : ‖u - c‖ ≤ 3 / (n : ℝ) := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
    have hp : (blaschkeNodePolynomial s x).eval u ≠ 0 := by
      apply (blaschkeNodePolynomial_eval_ne_zero_iff s x u).mpr
      intro i hi
      apply sub_ne_zero.mp
      exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num)
        (blaschkeFactor_endpoint_norm_lower (hx i hi) hc hci (hu'.trans hquarter)).1)
    exact (blaschkeDensity_analyticAt_of_nodePolynomial_ne_zero s x D hp).differentiableAt
  have hb : ∀ u ∈ Metric.closedBall c (3 / (n : ℝ)),
      ‖deriv (blaschkeDensity s x D) u‖ ≤ 4 * (n : ℝ) * Real.exp 12 := by
    intro u hu
    exact blaschkeDensity_endpoint_deriv_norm_le s x D n hn hD hcard hx hc hci
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu)
  exact Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_closedBall c _)
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw)

theorem blaschkeDensity_endpoint_difference_quotient_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx : ∀ i ∈ s, |x i| < 1)
    {c z w : ℂ} (hc : ‖c‖ = 1) (hci : |c.im| = 1)
    (hz : ‖z - c‖ ≤ 3 / (n : ℝ)) (hw : ‖w - c‖ ≤ 3 / (n : ℝ)) :
    ‖(blaschkeDensity s x D w - blaschkeDensity s x D z) / (w - z)‖ ≤
      4 * (n : ℝ) * Real.exp 12 := by
  by_cases heq : w = z
  · simp only [heq, sub_self, zero_div, norm_zero]
    positivity
  · rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr heq))).mpr
    exact blaschkeDensity_endpoint_difference_norm_le s x D n hn hD hcard hx hc hci hz hw

end InternalCatalan




open MeasureTheory Polynomial
open scoped Interval
namespace InternalCatalan

def blaschkeInterpolant {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (z : ℂ) : ℂ :=
  z ^ D - ((3 / Real.pi : ℝ) : ℂ) *
    (z ^ D * (cauchyLogLeft (1 + 2 / (n : ℝ)) z -
      blaschkeIntegratedDividedDifference s x (1 + 2 / (n : ℝ)) (blaschkeNodePolynomial s x) z) +
    finiteBlaschke s x z *
      blaschkeIntegratedDividedDifference s x (1 + 2 / (n : ℝ)) (blaschkeDensityNumerator s x D) z)

theorem blaschkeNodePolynomial_eval_node {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {i : ι} (hi : i ∈ s) : (blaschkeNodePolynomial s x).eval (x i : ℂ) = 0 := by
  by_contra h
  exact ((blaschkeNodePolynomial_eval_ne_zero_iff s x _).mp h i hi) rfl

theorem blaschkeIntegratedNodeDifference_eq_scalarIntegral {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (T : ℝ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z = 0) (hre : z.re ≠ 0) :
    blaschkeIntegratedDividedDifference s x T (blaschkeNodePolynomial s x) z =
      ∫ t in -T..T, (1 : ℂ) / (Complex.I * (t : ℂ) - z) := by
  rw [← integral_blaschkeDividedDifference_quotient s x hx]
  apply intervalIntegral.integral_congr
  intro t _
  have hid := sub_mul_polynomialDividedDifference (blaschkeNodePolynomial s x) z
    (Complex.I * (t : ℂ))
  rw [hz, sub_zero] at hid
  apply (div_eq_div_iff (blaschkeNodePolynomial_eval_imaginary_ne_zero s x hx t)
    (imaginary_sub_ne_zero_of_re_ne_zero hre t)).mpr
  simpa only [one_mul, mul_comm] using hid

theorem blaschkeInterpolant_analyticAt {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) {z : ℂ} (hden : ∀ i ∈ s, 1 - (x i : ℂ) * z ≠ 0)
    (hlo : -(1 + 2 / (n : ℝ)) < z.im) (hhi : z.im < 1 + 2 / (n : ℝ)) :
    AnalyticAt ℂ (blaschkeInterpolant s x D n) z := by
  unfold blaschkeInterpolant
  exact (analyticAt_id.pow D).sub (analyticAt_const.mul
    (((analyticAt_id.pow D).mul ((cauchyLogLeft_analyticAt hlo hhi).sub
      (blaschkeIntegratedDividedDifference_analyticAt _ _ _ _ _))).add
      ((finiteBlaschke_analyticAt s x hden).mul
        (blaschkeIntegratedDividedDifference_analyticAt _ _ _ _ _))))

theorem blaschkeInterpolant_analyticOnNhd_closedDisk {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hn : 0 < n) (hx : ∀ i ∈ s, |x i| < 1) :
    AnalyticOnNhd ℂ (blaschkeInterpolant s x D n) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  have hzn : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have him : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hzn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hrad : 1 < 1 + 2 / (n : ℝ) := by
    have hpos : (0 : ℝ) < 2 / (n : ℝ) := div_pos (by norm_num) hnR
    linarith
  have hstrip : |z.im| < 1 + 2 / (n : ℝ) := him.trans_lt hrad
  exact blaschkeInterpolant_analyticAt s x D n
    (fun i hi => blaschkeFactor_denominator_ne_zero (hx i hi) hzn)
    (abs_lt.mp hstrip).1 (abs_lt.mp hstrip).2

theorem blaschkeInterpolant_eval_negative_node {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {i : ι}
    (hi : i ∈ s) (hneg : x i < 0) :
    blaschkeInterpolant s x D n (x i : ℂ) = (x i : ℂ) ^ D := by
  have hre : (x i : ℂ).re < 0 := hneg
  have hUP := blaschkeIntegratedNodeDifference_eq_scalarIntegral s x (1 + 2 / (n : ℝ)) hx
    (blaschkeNodePolynomial_eval_node s x hi) hre.ne
  rw [integral_cauchyConstantKernel_eq_left _ hre] at hUP
  unfold blaschkeInterpolant
  rw [hUP, sub_self, finiteBlaschke_eval_node s x hi]
  ring

private theorem cauchy_coefficient_mul_two_pi :
    ((3 / Real.pi : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 6 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by
    intro h
    exact Real.pi_pos.ne' (by simpa using congrArg Complex.re h)
  rw [Complex.ofReal_div, Complex.ofReal_ofNat]
  field_simp [hp]
  ring

theorem blaschkeInterpolant_eval_positive_node {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {i : ι}
    (hi : i ∈ s) (hpos : 0 < x i) :
    blaschkeInterpolant s x D n (x i : ℂ) = -5 * (x i : ℂ) ^ D := by
  have hre : 0 < (x i : ℂ).re := hpos
  have hUP := blaschkeIntegratedNodeDifference_eq_scalarIntegral s x (1 + 2 / (n : ℝ)) hx
    (blaschkeNodePolynomial_eval_node s x hi) hre.ne'
  rw [integral_cauchyConstantKernel_eq_right _ hre] at hUP
  have hrad : (0 : ℝ) < 1 + 2 / (n : ℝ) := by positivity
  have hlo : -(1 + 2 / (n : ℝ)) < (x i : ℂ).im := by simpa only [Complex.ofReal_im] using (neg_lt_zero.mpr hrad)
  have hhi : (x i : ℂ).im < 1 + 2 / (n : ℝ) := by simpa using hrad
  unfold blaschkeInterpolant
  rw [hUP, cauchyLogLeft_sub_cauchyLogRight hlo hhi, finiteBlaschke_eval_node s x hi]
  calc
    _ = (x i : ℂ) ^ D -
        (((3 / Real.pi : ℝ) : ℂ) * (2 * (Real.pi : ℂ))) * (x i : ℂ) ^ D := by ring
    _ = -5 * (x i : ℂ) ^ D := by rw [cauchy_coefficient_mul_two_pi]; ring

theorem blaschkeInterpolant_eq_left_continuation {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) {z : ℂ} (hB : finiteBlaschke s x z ≠ 0) :
    blaschkeInterpolant s x D n z = z ^ D - finiteBlaschke s x z * blaschkeCauchyLeft s x D n z := by
  have hBF : finiteBlaschke s x z * blaschkeDensity s x D z = z ^ D := by
    unfold blaschkeDensity
    field_simp [hB]
  unfold blaschkeInterpolant blaschkeCauchyLeft blaschkeCauchyRemainder
  rw [← blaschkeDensity_eq_eval_div]
  calc
    _ = z ^ D - ((3 / Real.pi : ℝ) : ℂ) *
        ((finiteBlaschke s x z * blaschkeDensity s x D z) *
          (cauchyLogLeft (1 + 2 / (n : ℝ)) z -
            blaschkeIntegratedDividedDifference s x (1 + 2 / (n : ℝ)) (blaschkeNodePolynomial s x) z) +
        finiteBlaschke s x z *
          blaschkeIntegratedDividedDifference s x (1 + 2 / (n : ℝ)) (blaschkeDensityNumerator s x D) z) := by
            rw [hBF]
    _ = _ := by ring

theorem blaschkeInterpolant_eq_right_continuation {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) {z : ℂ} (hB : finiteBlaschke s x z ≠ 0)
    (hlo : -(1 + 2 / (n : ℝ)) < z.im) (hhi : z.im < 1 + 2 / (n : ℝ)) :
    blaschkeInterpolant s x D n z = -5 * z ^ D - finiteBlaschke s x z * blaschkeCauchyRight s x D n z := by
  have hBF : finiteBlaschke s x z * blaschkeDensity s x D z = z ^ D := by
    unfold blaschkeDensity
    field_simp [hB]
  have hj := blaschkeCauchyLeft_sub_right s x D n hlo hhi
  have heq : blaschkeCauchyLeft s x D n z =
      6 * blaschkeDensity s x D z + blaschkeCauchyRight s x D n z :=
    (sub_eq_iff_eq_add).mp hj
  rw [blaschkeInterpolant_eq_left_continuation s x D n hB, heq]
  calc
    _ = -5 * z ^ D - finiteBlaschke s x z * blaschkeCauchyRight s x D n z +
        6 * (z ^ D - finiteBlaschke s x z * blaschkeDensity s x D z) := by ring
    _ = _ := by rw [hBF]; ring

end InternalCatalan

end



noncomputable section
namespace InternalCatalan

theorem blaschkeNodePolynomial_ne_zero_on_circle {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, |x i| < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    (blaschkeNodePolynomial s x).eval z ≠ 0 := by
  apply (blaschkeNodePolynomial_eval_ne_zero_iff s x z).mpr
  intro i hi heq
  have hh := congrArg (fun w : ℂ => ‖w‖) heq
  rw [hz, Complex.norm_real, Real.norm_eq_abs] at hh
  exact (ne_of_lt (hx i hi)) hh.symm

theorem blaschkeDensity_norm_eq_one_on_circle {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (hx : ∀ i ∈ s, |x i| < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖blaschkeDensity s x D z‖ = 1 := by
  unfold blaschkeDensity
  rw [norm_div, norm_pow, hz, one_pow, finiteBlaschke_norm_eq_one s x hx hz, div_one]

private theorem circle_inside_cauchy_strip (n : ℕ) (hn : 0 < n) {z : ℂ} (hz : ‖z‖ = 1) :
    |z.im| < 1 + 2 / (n : ℝ) := by
  have hh : |z.im| ≤ 1 := by simpa only [hz] using Complex.abs_im_le_norm z
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : (0 : ℝ) < 2 / (n : ℝ) := div_pos (by norm_num) hnR
  linarith

theorem blaschkeInterpolant_circle_eq_left {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re < 0) :
    blaschkeInterpolant s x D n z = z ^ D - finiteBlaschke s x z * blaschkeCauchyTransform s x D n z := by
  have hB : finiteBlaschke s x z ≠ 0 := norm_pos_iff.mp
    (by rw [finiteBlaschke_norm_eq_one s x hx hz]; norm_num)
  rw [blaschkeInterpolant_eq_left_continuation s x D n hB,
    blaschkeCauchyTransform_eq_left s x D n hx0 (blaschkeNodePolynomial_ne_zero_on_circle s x hx hz) hre]

theorem blaschkeInterpolant_circle_eq_right {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hn : 0 < n) (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hre : 0 < z.re) :
    blaschkeInterpolant s x D n z = -5 * z ^ D - finiteBlaschke s x z * blaschkeCauchyTransform s x D n z := by
  have hB : finiteBlaschke s x z ≠ 0 := norm_pos_iff.mp
    (by rw [finiteBlaschke_norm_eq_one s x hx hz]; norm_num)
  have hs := abs_lt.mp (circle_inside_cauchy_strip n hn hz)
  rw [blaschkeInterpolant_eq_right_continuation s x D n hB hs.1 hs.2,
    blaschkeCauchyTransform_eq_right s x D n hx0 (blaschkeNodePolynomial_ne_zero_on_circle s x hx hz) hre]

theorem blaschkeInterpolant_circle_norm_le_five_add {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hn : 0 < n) (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re ≠ 0) :
    ‖blaschkeInterpolant s x D n z‖ ≤ 5 + ‖blaschkeCauchyTransform s x D n z‖ := by
  have hB := finiteBlaschke_norm_eq_one s x hx hz
  rcases lt_or_gt_of_ne hre with hre | hre
  · rw [blaschkeInterpolant_circle_eq_left s x D n hx0 hx hz hre]
    have hh := norm_sub_le (z ^ D) (finiteBlaschke s x z * blaschkeCauchyTransform s x D n z)
    simp only [norm_pow, hz, one_pow, norm_mul, hB, one_mul] at hh
    linarith
  · rw [blaschkeInterpolant_circle_eq_right s x D n hn hx0 hx hz hre]
    have hh := norm_sub_le (-5 * z ^ D) (finiteBlaschke s x z * blaschkeCauchyTransform s x D n z)
    simpa [norm_mul, norm_pow, hz, hB] using hh

theorem interpolant_far_axis_numerical (n : ℕ) (hn : 48 ≤ n) :
    5 + 30 * Real.exp 2 * (n : ℝ) ≤ 10 * Real.exp 12 * (n : ℝ) := by
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hE : 1 ≤ Real.exp 12 := Real.one_le_exp (by norm_num)
  have hten : 11 ≤ Real.exp 10 := by linarith [Real.add_one_le_exp 10]
  have heq : Real.exp 12 = Real.exp 2 * Real.exp 10 := by rw [← Real.exp_add]; norm_num
  have hratio : 11 * Real.exp 2 ≤ Real.exp 12 := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hten (Real.exp_pos 2).le]
  have hratio' : 30 * Real.exp 2 ≤ 3 * Real.exp 12 := by nlinarith [Real.exp_pos 2]
  have hrn := mul_le_mul_of_nonneg_right hratio' (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hEn := mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

theorem interpolant_near_axis_numerical (n : ℕ) (hn : 48 ≤ n) :
    5 + (6 * Real.exp 2 * (n : ℝ) + 12 * Real.exp 12 + 3 * (n : ℝ)) ≤
      10 * Real.exp 12 * (n : ℝ) := by
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hE : 1 ≤ Real.exp 12 := Real.one_le_exp (by norm_num)
  have h2 : Real.exp 2 ≤ Real.exp 12 := Real.exp_le_exp.mpr (by norm_num)
  have h2n := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hEn := mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have h17n : 17 * Real.exp 12 ≤ (n : ℝ) * Real.exp 12 :=
    mul_le_mul_of_nonneg_right (by linarith : (17 : ℝ) ≤ n) (Real.exp_pos 12).le
  nlinarith

end InternalCatalan




open MeasureTheory Set
open scoped BigOperators Interval
namespace InternalCatalan

theorem blaschkeCauchyKernel_local_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx0 : ∀ i ∈ s, x i ≠ 0)
    (hx : ∀ i ∈ s, |x i| < 1) (a b : ℝ) (hab : a ≤ b)
    (hlen : b - a ≤ 3 / (n : ℝ)) {c z : ℂ}
    (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hz : ‖z‖ = 1) (hre : z.re ≠ 0)
    (hzc : ‖z - c‖ ≤ 3 / (n : ℝ))
    (hpath : ∀ t ∈ Icc a b, ‖Complex.I * (t : ℂ) - c‖ ≤ 3 / (n : ℝ))
    (hal : 1 / (2 * (n : ℝ)) ≤ ‖Complex.I * (a : ℂ) - z‖)
    (hau : ‖Complex.I * (a : ℂ) - z‖ ≤ 1)
    (hbl : 1 / (2 * (n : ℝ)) ≤ ‖Complex.I * (b : ℂ) - z‖)
    (hbu : ‖Complex.I * (b : ℂ) - z‖ ≤ 1) :
    ‖∫ t in a..b, blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)‖ ≤ 12 * Real.exp 12 + 3 * (n : ℝ) := by
  let g : ℝ → ℂ := fun t =>
    (blaschkeDensity s x D (Complex.I * (t : ℂ)) - blaschkeDensity s x D z) /
      (Complex.I * (t : ℂ) - z)
  have hgc : Continuous g :=
    ((continuous_blaschkeDensity_imaginary s x D hx0).sub continuous_const).div
      ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const)
      (imaginary_sub_ne_zero_of_re_ne_zero hre)
  have hgi : IntervalIntegrable g volume a b := hgc.intervalIntegrable _ _
  have hsc : IntervalIntegrable (fun t : ℝ => blaschkeDensity s x D z *
      (1 / (Complex.I * (t : ℂ) - z))) volume a b :=
    (intervalIntegrable_cauchyConstantKernel_interval a b hre).const_mul _
  have hfun : (fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)) =
      (fun t : ℝ => g t + blaschkeDensity s x D z * (1 / (Complex.I * (t : ℂ) - z))) := by
    funext t
    dsimp only [g]
    ring
  have hgb : ‖∫ t in a..b, g t‖ ≤ 12 * Real.exp 12 := by
    have hi : ‖∫ t in a..b, g t‖ ≤ (4 * (n : ℝ) * Real.exp 12) * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hab] at ht
      exact blaschkeDensity_endpoint_difference_quotient_norm_le s x D n hn hD hcard hx
        hc hci hzc (hpath t ⟨ht.1.le, ht.2⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
    have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 48) hn)
    calc
      _ ≤ (4 * (n : ℝ) * Real.exp 12) * (b - a) := hi
      _ ≤ (4 * (n : ℝ) * Real.exp 12) * (3 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = 12 * Real.exp 12 := by field_simp [hnR.ne']; ring
  rw [hfun, intervalIntegral.integral_add hgi hsc, intervalIntegral.integral_const_mul]
  calc
    _ ≤ ‖∫ t in a..b, g t‖ +
        ‖blaschkeDensity s x D z * (∫ t in a..b, (1 : ℂ) / (Complex.I * (t : ℂ) - z))‖ := norm_add_le _ _
    _ ≤ 12 * Real.exp 12 + 3 * (n : ℝ) := by
      rw [norm_mul, blaschkeDensity_norm_eq_one_on_circle s x D hx hz, one_mul]
      exact add_le_add hgb (cauchyConstantKernel_interval_norm_le_three_mul n hn a b hre hal hau hbl hbu)

theorem blaschkeCauchyKernel_far_piece_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hx : ∀ i ∈ s, x i ^ 2 ≤ 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    (a b : ℝ) (hab : a ≤ b) (hlen : b - a ≤ 3) {z : ℂ}
    (hpath : ∀ t ∈ Icc a b, |t| ≤ 1 + 2 / (n : ℝ))
    (hsep : ∀ t ∈ Icc a b, 1 / (2 * (n : ℝ)) ≤ ‖Complex.I * (t : ℂ) - z‖) :
    ‖∫ t in a..b, blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)‖ ≤ 6 * Real.exp 2 * (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 48) hn)
  have hi : ‖∫ t in a..b, blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)‖ ≤ (2 * Real.exp 2 * (n : ℝ)) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le hab] at ht
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    have hp : (0 : ℝ) < ‖Complex.I * (t : ℂ) - z‖ :=
      lt_of_lt_of_le (by positivity) (hsep t ht')
    have hF : ‖blaschkeDensity s x D (Complex.I * (t : ℂ))‖ ≤ Real.exp 2 :=
      finiteBlaschke_diameter_quotient_le_exp_two s x D n hDpos hD hx hweight (hpath t ht')
    rw [norm_div]
    apply (div_le_iff₀ hp).mpr
    have hs := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))).mp (hsep t ht')
    have hm := mul_le_mul_of_nonneg_left hs (Real.exp_pos 2).le
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  calc
    _ ≤ (2 * Real.exp 2 * (n : ℝ)) * (b - a) := hi
    _ ≤ (2 * Real.exp 2 * (n : ℝ)) * 3 := mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = 6 * Real.exp 2 * (n : ℝ) := by ring

end InternalCatalan

end



noncomputable section
open MeasureTheory Set
open scoped BigOperators Interval
namespace InternalCatalan

theorem blaschkeCauchyTransform_norm_le_split {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hx0 : ∀ i ∈ s, x i ≠ 0) {z : ℂ} (hre : z.re ≠ 0) (a : ℝ) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤
      ‖∫ t in -(1 + 2 / (n : ℝ))..a, blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)‖ +
      ‖∫ t in a..(1 + 2 / (n : ℝ)), blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)‖ := by
  have hc := continuous_blaschkeCauchyKernel s x D hx0 hre
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-(1 + 2 / (n : ℝ))) a)
    (hc.intervalIntegrable a (1 + 2 / (n : ℝ)))
  have hcoeff : ‖((3 / Real.pi : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_three]
  rw [blaschkeCauchyTransform_normalized, norm_mul, ← hi]
  calc
    _ ≤ 1 * ‖(∫ t in -(1 + 2 / (n : ℝ))..a,
        blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)) +
        (∫ t in a..(1 + 2 / (n : ℝ)),
          blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z))‖ :=
      mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    _ ≤ _ := by
      simpa only [one_mul] using
        (norm_add_le
          (∫ t in -(1 + 2 / (n : ℝ))..a,
            blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z))
          (∫ t in a..(1 + 2 / (n : ℝ)),
            blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)))

theorem blaschkeCauchyTransform_upper_crossing_bound {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re ≠ 0)
    (hnear : |z.re| ≤ 1 / (10 * (n : ℝ))) (him : 0 ≤ z.im) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤
      6 * Real.exp 2 * (n : ℝ) + 12 * Real.exp 12 + 3 * (n : ℝ) := by
  let r : ℝ := 1 / (n : ℝ)
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrsmall : r ≤ (1 / 48 : ℝ) := by
    dsimp only [r]
    apply (div_le_iff₀ hnpos).mpr
    linarith
  have hT : 1 + 2 / (n : ℝ) = 1 + 2 * r := by dsimp [r]; ring
  have h3 : 3 / (n : ℝ) = 3 * r := by dsimp [r]; ring
  have hhalf : 1 / (2 * (n : ℝ)) = r / 2 := by dsimp [r]; field_simp [hnpos.ne']
  have hnear' : |z.re| ≤ r / 10 := by
    convert! hnear using 1
    dsimp [r]
    field_simp [hnpos.ne']
  have hloc := upper_circle_crossing_location hz him hnear'
  have hend := upper_crossing_endpoint_distances hr hrsmall hz him hnear'
  have hsq : ∀ i ∈ s, x i ^ 2 ≤ 1 := by
    intro i hi
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (x i)) (hx i hi).le 2
  have hlocal : ‖∫ t in (1 - r)..(1 + 2 * r),
      blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖ ≤
      12 * Real.exp 12 + 3 * (n : ℝ) := by
    apply blaschkeCauchyKernel_local_norm_le s x D n hn hD hcard hx0 hx
      (1 - r) (1 + 2 * r) (by linarith) (by rw [h3]; linarith)
      (c := Complex.I) (by simp) (by simp) hz hre
    · rw [h3]; linarith [hloc.2.2]
    · intro t ht
      rw [h3]
      exact (upper_crossing_local_path hr ht.1 ht.2).trans (by linarith)
    · rw [hhalf]; exact hend.1.1
    · exact hend.1.2
    · rw [hhalf]; exact hend.2.1
    · exact hend.2.2
  have hfar : ‖∫ t in -(1 + 2 * r)..(1 - r),
      blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖ ≤
      6 * Real.exp 2 * (n : ℝ) := by
    apply blaschkeCauchyKernel_far_piece_norm_le s x D n hn hDpos hD hsq hweight
      (-(1 + 2 * r)) (1 - r) (by linarith) (by linarith)
    · intro t ht
      rw [hT]
      exact abs_le.mpr ⟨ht.1, by linarith [ht.2]⟩
    · intro t ht
      rw [hhalf]
      exact upper_crossing_far_separation hr hloc.1 ht.2
  have hsplit := blaschkeCauchyTransform_norm_le_split s x D n hx0 hre (1 - r)
  rw [hT] at hsplit
  linarith

theorem blaschkeCauchyTransform_lower_crossing_bound {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re ≠ 0)
    (hnear : |z.re| ≤ 1 / (10 * (n : ℝ))) (him : z.im ≤ 0) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤
      6 * Real.exp 2 * (n : ℝ) + 12 * Real.exp 12 + 3 * (n : ℝ) := by
  let r : ℝ := 1 / (n : ℝ)
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrsmall : r ≤ (1 / 48 : ℝ) := by
    dsimp only [r]
    apply (div_le_iff₀ hnpos).mpr
    linarith
  have hT : 1 + 2 / (n : ℝ) = 1 + 2 * r := by dsimp [r]; ring
  have h3 : 3 / (n : ℝ) = 3 * r := by dsimp [r]; ring
  have hhalf : 1 / (2 * (n : ℝ)) = r / 2 := by dsimp [r]; field_simp [hnpos.ne']
  have hnear' : |z.re| ≤ r / 10 := by
    convert! hnear using 1
    dsimp [r]
    field_simp [hnpos.ne']
  have hloc := lower_circle_crossing_location hz him hnear'
  have hend := lower_crossing_endpoint_distances hr hrsmall hz him hnear'
  have hsq : ∀ i ∈ s, x i ^ 2 ≤ 1 := by
    intro i hi
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (x i)) (hx i hi).le 2
  have hlocal : ‖∫ t in -(1 + 2 * r)..(-1 + r),
      blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖ ≤
      12 * Real.exp 12 + 3 * (n : ℝ) := by
    rw [show -(1 + 2 * r) = -1 - 2 * r by ring]
    apply blaschkeCauchyKernel_local_norm_le s x D n hn hD hcard hx0 hx
      (-1 - 2 * r) (-1 + r) (by linarith) (by rw [h3]; linarith)
      (c := -Complex.I) (by simp) (by simp) hz hre
    · rw [sub_neg_eq_add, h3]; linarith [hloc.2.2]
    · intro t ht
      rw [sub_neg_eq_add, h3]
      exact (lower_crossing_local_path hr ht.1 ht.2).trans (by linarith)
    · rw [hhalf]; exact hend.1.1
    · exact hend.1.2
    · rw [hhalf]; exact hend.2.1
    · exact hend.2.2
  have hfar : ‖∫ t in (-1 + r)..(1 + 2 * r),
      blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖ ≤
      6 * Real.exp 2 * (n : ℝ) := by
    apply blaschkeCauchyKernel_far_piece_norm_le s x D n hn hDpos hD hsq hweight
      (-1 + r) (1 + 2 * r) (by linarith) (by linarith)
    · intro t ht
      rw [hT]
      exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    · intro t ht
      rw [hhalf]
      exact lower_crossing_far_separation hr hloc.2.1 ht.1
  have hsplit := blaschkeCauchyTransform_norm_le_split s x D n hx0 hre (-1 + r)
  rw [hT] at hsplit
  linarith

theorem blaschkeCauchyTransform_near_axis_bound {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re ≠ 0) (hnear : |z.re| ≤ 1 / (10 * (n : ℝ))) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤
      6 * Real.exp 2 * (n : ℝ) + 12 * Real.exp 12 + 3 * (n : ℝ) := by
  rcases le_total 0 z.im with him | him
  · exact blaschkeCauchyTransform_upper_crossing_bound s x D n hn hDpos hD hcard hx0 hx hweight hz hre hnear him
  · exact blaschkeCauchyTransform_lower_crossing_bound s x D n hn hDpos hD hcard hx0 hx hweight hz hre hnear him

end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan

theorem blaschkeInterpolant_boundary_norm_le_off_axis {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re ≠ 0) :
    ‖blaschkeInterpolant s x D n z‖ ≤ 10 * Real.exp 12 * (n : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbase := blaschkeInterpolant_circle_norm_le_five_add s x D n hn0 hx0 hx hz hre
  by_cases hfar : 1 / (10 * (n : ℝ)) ≤ |z.re|
  · have hsq : ∀ i ∈ s, x i ^ 2 ≤ 1 := by
      intro i hi
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (x i)) (hx i hi).le 2
    exact (hbase.trans (add_le_add (le_refl 5)
      (blaschkeCauchyTransform_far_axis_bound s x D n hn hDpos hD hsq hweight hfar))).trans
      (interpolant_far_axis_numerical n hn)
  · have hnear : |z.re| ≤ 1 / (10 * (n : ℝ)) := (lt_of_not_ge hfar).le
    exact (hbase.trans (add_le_add (le_refl 5)
      (blaschkeCauchyTransform_near_axis_bound s x D n hn hDpos hD hcard hx0 hx hweight hz hre hnear))).trans
      (interpolant_near_axis_numerical n hn)

end InternalCatalan

end



noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace InternalCatalan

theorem blaschkeInterpolant_boundary_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖blaschkeInterpolant s x D n z‖ ≤ 10 * Real.exp 12 * (n : ℝ) := by
  by_cases hre : z.re ≠ 0
  · exact blaschkeInterpolant_boundary_norm_le_off_axis s x D n hn hDpos hD hcard hx0 hx hweight hz hre
  have hre0 : z.re = 0 := not_ne_iff.mp hre
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hA := blaschkeInterpolant_analyticOnNhd_closedDisk s x D n hn0 hx
  have hzclosed : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, hz, le_refl]
  have hcont : ContinuousAt (fun w : ℂ => ‖blaschkeInterpolant s x D n w‖) z :=
    (hA z hzclosed).continuousAt.norm
  have hcomp : ContinuousAt (fun t : ℝ =>
      ‖blaschkeInterpolant s x D n (circleRightPerturb z t)‖) 0 := by
    simpa only [Function.comp_def] using hcont.comp_of_eq
      (f := circleRightPerturb z) (circleRightPerturb_continuousAt_zero hz) (circleRightPerturb_zero hz)
  have ht : Tendsto (fun t : ℝ => ‖blaschkeInterpolant s x D n (circleRightPerturb z t)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖blaschkeInterpolant s x D n z‖) := by
    simpa only [circleRightPerturb_zero hz] using
      hcomp.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply le_of_tendsto ht
  exact (show ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioi 0 from self_mem_nhdsWithin).mono (fun t ht => by
    have hp := circleRightPerturb_norm_and_re hre0 ht
    exact blaschkeInterpolant_boundary_norm_le_off_axis s x D n hn hDpos hD hcard hx0 hx hweight hp.1 hp.2)

theorem blaschkeInterpolant_closedDisk_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖blaschkeInterpolant s x D n z‖ ≤ 10 * Real.exp 12 * (n : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hA := blaschkeInterpolant_analyticOnNhd_closedDisk s x D n hn0 hx
  have hd : DiffContOnCl ℂ (blaschkeInterpolant s x D n) (Metric.ball (0 : ℂ) 1) :=
    hA.differentiableOn.diffContOnCl_ball Set.Subset.rfl
  refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd ?_ ?_
  · intro w hw
    apply blaschkeInterpolant_boundary_norm_le s x D n hn hDpos hD hcard hx0 hx hweight
    simpa only [frontier_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0),
      Metric.mem_sphere, dist_zero_right] using hw
  · simpa only [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)] using hz

theorem real_uniform_interpolation_actual {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ)) :
    ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ i ∈ s, h (x i : ℂ) = if x i < 0 then (x i : ℂ) ^ D else -5 * (x i : ℂ) ^ D) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖h z‖ ≤ 10 * Real.exp 12 * (n : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  refine ⟨blaschkeInterpolant s x D n,
    blaschkeInterpolant_analyticOnNhd_closedDisk s x D n hn0 hx, ?_, ?_⟩
  · intro i hi
    by_cases hneg : x i < 0
    · rw [if_pos hneg]
      exact blaschkeInterpolant_eval_negative_node s x D n hx0 hi hneg
    · rw [if_neg hneg]
      exact blaschkeInterpolant_eval_positive_node s x D n hx0 hi
        ((lt_or_gt_of_ne (hx0 i hi)).resolve_left hneg)
  · intro z hz
    exact blaschkeInterpolant_closedDisk_norm_le s x D n hn hDpos hD hcard hx0 hx hweight hz

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.RealTwoSheetIntegralBound
namespace OAI


noncomputable section

namespace InternalCatalan

open Complex Metric MeasureTheory
open scoped ComplexConjugate

abbrev FirstSheetBoundaryL2 := Lp ℂ 2 firstSheetBoundaryMeasure

def firstSheetBoundaryToLp : C(Circle, ℂ) →L[ℂ] FirstSheetBoundaryL2 :=
  ContinuousMap.toLp 2 firstSheetBoundaryMeasure ℂ

def firstSheetBoundaryVector (u : ℂ → ℂ)
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) : FirstSheetBoundaryL2 :=
  firstSheetBoundaryToLp (firstSheetBoundaryFunction u hu)

theorem firstSheetBoundary_inner (f g : C(Circle, ℂ)) :
    inner ℂ (firstSheetBoundaryToLp f) (firstSheetBoundaryToLp g) =
      ∫ z : Circle, g z * conj (f z) ∂firstSheetBoundaryMeasure := by
  exact MeasureTheory.ContinuousMap.inner_toLp firstSheetBoundaryMeasure f g

theorem firstSheetBoundary_inner_function {u v : ℂ → ℂ}
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1))
    (hv : ContinuousOn v (closedBall (0 : ℂ) 1)) :
    inner ℂ (firstSheetBoundaryVector u hu) (firstSheetBoundaryVector v hv) =
      Real.circleAverage (fun z => v z * conj (u z)) 0 1 := by
  rw [firstSheetBoundaryVector, firstSheetBoundaryVector, firstSheetBoundary_inner]
  exact firstSheetBoundary_integral
    (hv.mul (Complex.continuous_conj.comp_continuousOn hu))

theorem firstSheetBoundary_norm_sq (f : C(Circle, ℂ)) :
    ‖firstSheetBoundaryToLp f‖ ^ 2 =
      ∫ z : Circle, ‖f z‖ ^ 2 ∂firstSheetBoundaryMeasure := by
  have h := firstSheetBoundary_inner f f
  simp only [inner_self_eq_norm_sq_to_K, Complex.mul_conj',
    ← Complex.ofReal_pow, integral_complex_ofReal] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow]
  exact h

theorem firstSheetBoundary_norm_sq_function {u : ℂ → ℂ}
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) :
    ‖firstSheetBoundaryVector u hu‖ ^ 2 =
      Real.circleAverage (fun z => ‖u z‖ ^ 2) 0 1 := by
  rw [firstSheetBoundaryVector, firstSheetBoundary_norm_sq]
  exact firstSheetBoundary_integral (hu.norm.pow 2)

def firstSheetKernelVector (x : ℝ) (hx : |x| < 1) : FirstSheetBoundaryL2 :=
  firstSheetBoundaryVector (firstSheetKernel x)
    (firstSheetKernel_continuousOn_closedDisk hx)

theorem firstSheetBoundary_inner_kernel {u : ℂ → ℂ}
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) 1)) {x : ℝ} (hx : |x| < 1) :
    inner ℂ (firstSheetKernelVector x hx)
      (firstSheetBoundaryVector u hu.continuousOn) = u x := by
  unfold firstSheetKernelVector
  rw [firstSheetBoundary_inner_function]
  exact circleAverage_mul_conj_firstSheetKernel hu hx

end InternalCatalan

end



noncomputable section
open scoped BigOperators ComplexConjugate
namespace InternalCatalan

def firstSheetNumerator {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ k : Fin n, a k * z ^ (k : ℕ)

def firstSheetDenominator {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, (1 - (x i : ℂ) * z)

def firstSheetRational {ι : Type*} {n : ℕ} (s : Finset ι) (x : ι → ℝ)
    (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  firstSheetNumerator a z / firstSheetDenominator s x z

def firstSheetReverse (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun a k := a k.rev
  invFun a k := a k.rev
  left_inv a := by funext k; simp only [Fin.rev_rev]
  right_inv a := by funext k; simp only [Fin.rev_rev]
  map_add' a b := rfl
  map_smul' c a := rfl

def firstSheetBoundaryNormSq {ι : Type*} {n : ℕ} (s : Finset ι) (x : ι → ℝ)
    (a : Fin n → ℂ) : ℝ :=
  Real.circleAverage (fun z => ‖firstSheetRational s x a z‖ ^ 2) 0 1

theorem firstSheetReverse_involutive (n : ℕ) (a : Fin n → ℂ) :
    firstSheetReverse n (firstSheetReverse n a) = a := by
  funext k
  change a k.rev.rev = a k
  rw [Fin.rev_rev]

theorem firstSheetDenominator_ne_zero {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, |x i| < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    firstSheetDenominator s x z ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr
    (fun i hi => blaschkeFactor_denominator_ne_zero (hx i hi) hz)

theorem firstSheetDenominator_conj {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) :
    firstSheetDenominator s x (conj z) = conj (firstSheetDenominator s x z) := by
  simp only [firstSheetDenominator, map_prod, map_sub, map_one, map_mul, Complex.conj_ofReal]

theorem firstSheetDenominator_norm_inv {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖firstSheetDenominator s x z⁻¹‖ = ‖firstSheetDenominator s x z‖ := by
  rw [Complex.inv_eq_conj hz, firstSheetDenominator_conj, Complex.norm_conj]

theorem firstSheetNumerator_reverse {n : ℕ} (a : Fin n → ℂ) {z : ℂ} (hz : z ≠ 0) :
    firstSheetNumerator (firstSheetReverse n a) z =
      z ^ (n - 1) * firstSheetNumerator a z⁻¹ := by
  have hreindex : firstSheetNumerator (firstSheetReverse n a) z =
      ∑ k : Fin n, a k * z ^ (k.rev : ℕ) := by
    change (∑ k : Fin n, a k.rev * z ^ (k : ℕ)) = _
    simpa only [Fin.revPerm_apply, Fin.rev_rev] using
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
        (fun k : Fin n => a k * z ^ (k.rev : ℕ)))
  rw [hreindex, firstSheetNumerator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k.rev : ℕ) + (k : ℕ) = n - 1 := by
    simp only [Fin.val_rev]
    omega
  calc
    a k * z ^ (k.rev : ℕ) = z ^ ((k.rev : ℕ) + (k : ℕ)) *
        (a k * (z⁻¹) ^ (k : ℕ)) := by
      rw [pow_add, inv_pow]
      field_simp [hz]
    _ = z ^ (n - 1) * (a k * (z⁻¹) ^ (k : ℕ)) := by rw [hk]

theorem firstSheetNumerator_reverse_norm {n : ℕ} (a : Fin n → ℂ)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖firstSheetNumerator (firstSheetReverse n a) z‖ = ‖firstSheetNumerator a z⁻¹‖ := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [firstSheetNumerator_reverse a hz0, norm_mul, norm_pow, hz, one_pow, one_mul]

theorem firstSheetRational_reverse_norm {ι : Type*} {n : ℕ}
    (s : Finset ι) (x : ι → ℝ) (a : Fin n → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖firstSheetRational s x (firstSheetReverse n a) z‖ =
      ‖firstSheetRational s x a z⁻¹‖ := by
  rw [firstSheetRational, firstSheetRational, norm_div, norm_div,
    firstSheetNumerator_reverse_norm a hz, firstSheetDenominator_norm_inv s x hz]

theorem firstSheetBoundaryNormSq_reverse {ι : Type*} {n : ℕ}
    (s : Finset ι) (x : ι → ℝ) (a : Fin n → ℂ) :
    firstSheetBoundaryNormSq s x (firstSheetReverse n a) = firstSheetBoundaryNormSq s x a := by
  unfold firstSheetBoundaryNormSq
  calc
    _ = Real.circleAverage (fun z => ‖firstSheetRational s x a z⁻¹‖ ^ 2) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hzn : ‖z‖ = 1 := by simpa only [abs_one, Metric.mem_sphere, dist_zero_right] using hz
      convert! congrArg (fun r : ℝ => r ^ 2) (firstSheetRational_reverse_norm s x a hzn) using 1
    _ = _ := by
      convert! (Real.circleAverage_zero_one_congr_inv
        (f := fun z : ℂ => ‖firstSheetRational s x a z‖ ^ 2)) using 1

theorem firstSheetNumerator_analyticAt {n : ℕ} (a : Fin n → ℂ) (z : ℂ) :
    AnalyticAt ℂ (firstSheetNumerator a) z := by
  unfold firstSheetNumerator
  apply Finset.analyticAt_fun_sum
  intro k _
  exact analyticAt_const.mul (analyticAt_id.pow (k : ℕ))

theorem firstSheetDenominator_analyticAt {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) :
    AnalyticAt ℂ (firstSheetDenominator s x) z := by
  unfold firstSheetDenominator
  apply Finset.analyticAt_fun_prod
  intro i _
  exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)

theorem firstSheetRational_analyticOnNhd_closedDisk {ι : Type*} {n : ℕ}
    (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, |x i| < 1) (a : Fin n → ℂ) :
    AnalyticOnNhd ℂ (firstSheetRational s x a) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  exact (firstSheetNumerator_analyticAt a z).div (firstSheetDenominator_analyticAt s x z)
    (firstSheetDenominator_ne_zero s x hx (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz))

end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan

def firstSheetEvaluation {n : ℕ} (x : Fin n → ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  (Matrix.vandermonde (fun i => (x i : ℂ))).mulVecLin

theorem firstSheetEvaluation_apply {n : ℕ} (x : Fin n → ℝ) (a : Fin n → ℂ) (i : Fin n) :
    firstSheetEvaluation x a i = firstSheetNumerator a (x i : ℂ) := by
  simp only [firstSheetEvaluation, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.vandermonde_apply, firstSheetNumerator, mul_comm]

theorem firstSheetEvaluation_det_ne_zero {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) : (Matrix.vandermonde (fun i => (x i : ℂ))).det ≠ 0 := by
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j h
  exact hx (Complex.ofReal_injective h)

def firstSheetEvaluationEquiv {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) :
    (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin n))
    (Matrix.vandermonde (fun i => (x i : ℂ)))
    (isUnit_iff_ne_zero.mpr (firstSheetEvaluation_det_ne_zero x hx))

theorem firstSheetEvaluationEquiv_apply {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (a : Fin n → ℂ) (i : Fin n) :
    firstSheetEvaluationEquiv x hx a i = firstSheetNumerator a (x i : ℂ) := by
  change (Matrix.toLin (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))
    (Matrix.vandermonde (fun j => (x j : ℂ))) a) i = _
  rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  exact firstSheetEvaluation_apply x a i


theorem firstSheetEvaluation_eq_denominator_mul_value {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (a : Fin n → ℂ) (i : Fin n) :
    firstSheetEvaluation x a i = firstSheetDenominator Finset.univ x (x i : ℂ) *
      firstSheetRational Finset.univ x a (x i : ℂ) := by
  have hden := firstSheetDenominator_ne_zero Finset.univ x (fun j _ => hx j)
    (show ‖(x i : ℂ)‖ ≤ 1 by simpa only [Complex.norm_real, Real.norm_eq_abs] using (hx i).le)
  rw [firstSheetEvaluation_apply, firstSheetRational]
  field_simp

def firstSheetNodeMultiplier {n : ℕ} (x : Fin n → ℝ) (h : ℂ → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun a i := h (x i : ℂ) * a i
  map_add' a b := by ext i; exact mul_add _ _ _
  map_smul' c a := by ext i; change h (x i : ℂ) * (c * a i) = c * (h (x i : ℂ) * a i); ring

def firstSheetInterpolatingMultiplier {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (h : ℂ → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  (firstSheetEvaluationEquiv x hx).symm.toLinearMap.comp
    ((firstSheetNodeMultiplier x h).comp (firstSheetEvaluationEquiv x hx).toLinearMap)

theorem firstSheetInterpolatingMultiplier_eval {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (h : ℂ → ℂ) (a : Fin n → ℂ) (i : Fin n) :
    firstSheetNumerator (firstSheetInterpolatingMultiplier x hx h a) (x i : ℂ) =
      h (x i : ℂ) * firstSheetNumerator a (x i : ℂ) := by
  rw [← firstSheetEvaluationEquiv_apply x hx]
  change firstSheetEvaluationEquiv x hx
    ((firstSheetEvaluationEquiv x hx).symm
      (firstSheetNodeMultiplier x h (firstSheetEvaluationEquiv x hx a))) i = _
  rw [LinearEquiv.apply_symm_apply]
  change h (x i : ℂ) * firstSheetEvaluationEquiv x hx a i = _
  rw [firstSheetEvaluationEquiv_apply]

def firstSheetEvaluationOperator {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (h : ℂ → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.id + (firstSheetInterpolatingMultiplier x hx h).comp (firstSheetReverse n).toLinearMap

theorem firstSheetEvaluation_cancellation {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (h : ℂ → ℂ) (a : Fin n → ℂ) (i : Fin n) :
    firstSheetEvaluation x
      (firstSheetEvaluationOperator x hx h (firstSheetReverse n a)) i =
      firstSheetNumerator (firstSheetReverse n a) (x i : ℂ) +
        h (x i : ℂ) * firstSheetNumerator a (x i : ℂ) := by
  have hnumadd (a b : Fin n → ℂ) (z : ℂ) :
      firstSheetNumerator (a + b) z = firstSheetNumerator a z + firstSheetNumerator b z := by
    simp only [firstSheetNumerator, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [firstSheetEvaluation_apply]
  change firstSheetNumerator (firstSheetReverse n a +
    firstSheetInterpolatingMultiplier x hx h (firstSheetReverse n (firstSheetReverse n a))) _ = _
  rw [firstSheetReverse_involutive, hnumadd, firstSheetInterpolatingMultiplier_eval]

end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan

def firstSheetMixedEvaluationMatrix {n : ℕ} (x : Fin n → ℝ) (h : ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i k => (x i : ℂ) ^ (k.rev : ℕ) + h (x i : ℂ) * (x i : ℂ) ^ (k : ℕ))

theorem firstSheetNumerator_single {n : ℕ} (k : Fin n) (z : ℂ) :
    firstSheetNumerator (Pi.single k (1 : ℂ)) z = z ^ (k : ℕ) := by
  classical
  simp [firstSheetNumerator, Pi.single_apply]

theorem firstSheetReverse_single {n : ℕ} (k : Fin n) :
    firstSheetReverse n (Pi.single k (1 : ℂ)) = Pi.single k.rev 1 := by
  classical
  ext j
  change (Pi.single k (1 : ℂ) : Fin n → ℂ) j.rev = (Pi.single k.rev (1 : ℂ) : Fin n → ℂ) j
  simp only [Pi.single_apply, eq_comm]
  by_cases hj : j = k.rev
  · subst j
    simp
  · have hk : k ≠ j.rev := by
      intro h
      apply hj
      simpa only [Fin.rev_rev] using (congrArg Fin.rev h).symm
    simp only [hj, hk, ite_false]

theorem firstSheetMixedEvaluationMatrix_eq {n : ℕ} (x : Fin n → ℝ)
    (hxi : Function.Injective x) (h : ℂ → ℂ) :
    firstSheetMixedEvaluationMatrix x h = LinearMap.toMatrix'
      ((firstSheetEvaluation x).comp
        ((firstSheetEvaluationOperator x hxi h).comp (firstSheetReverse n).toLinearMap)) := by
  ext i k
  rw [LinearMap.toMatrix'_apply]
  change _ = firstSheetEvaluation x
    (firstSheetEvaluationOperator x hxi h (firstSheetReverse n (Pi.single k 1))) i
  rw [firstSheetEvaluation_cancellation, firstSheetReverse_single, firstSheetNumerator_single,
    firstSheetNumerator_single]
  rfl

theorem firstSheetReverse_det_norm (n : ℕ) :
    ‖LinearMap.det (firstSheetReverse n).toLinearMap‖ = 1 := by
  have hc : (firstSheetReverse n).toLinearMap.comp (firstSheetReverse n).toLinearMap =
      (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
    apply LinearMap.ext
    intro a
    exact firstSheetReverse_involutive n a
  have hd := congrArg LinearMap.det hc
  rw [LinearMap.det_comp, LinearMap.det_id] at hd
  have hn := congrArg norm hd
  rw [norm_mul, norm_one] at hn
  nlinarith [norm_nonneg (LinearMap.det (firstSheetReverse n).toLinearMap)]

theorem firstSheetEvaluation_det {n : ℕ} (x : Fin n → ℝ) :
    LinearMap.det (firstSheetEvaluation x) =
      (Matrix.vandermonde (fun i => (x i : ℂ))).det := by
  unfold firstSheetEvaluation
  rw [← Matrix.toLin'_apply']
  exact LinearMap.det_toLin' _

theorem firstSheetMixedEvaluationMatrix_det {n : ℕ} (x : Fin n → ℝ)
    (hxi : Function.Injective x) (h : ℂ → ℂ) :
    (firstSheetMixedEvaluationMatrix x h).det =
      (Matrix.vandermonde (fun i => (x i : ℂ))).det *
        LinearMap.det (firstSheetEvaluationOperator x hxi h) *
          LinearMap.det (firstSheetReverse n).toLinearMap := by
  rw [firstSheetMixedEvaluationMatrix_eq x hxi]
  rw [LinearMap.det_toMatrix', LinearMap.det_comp, LinearMap.det_comp, firstSheetEvaluation_det]
  ring


end InternalCatalan

end



noncomputable section
open Polynomial
open scoped BigOperators
namespace InternalCatalan

def firstSheetKernelNumerator {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℂ[X] :=
  ∏ j ∈ Finset.univ.erase i, (1 - C (x j : ℂ) * X)

def firstSheetKernelCoefficients {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : Fin n → ℂ :=
  fun k => (firstSheetKernelNumerator x i).coeff (k : ℕ)

theorem firstSheetNumerator_coefficients {n : ℕ} (p : ℂ[X]) (hp : p.natDegree < n) (z : ℂ) :
    firstSheetNumerator (fun k : Fin n => p.coeff (k : ℕ)) z = p.eval z := by
  change (∑ k : Fin n, p.coeff (k : ℕ) * z ^ (k : ℕ)) = _
  calc
    _ = ∑ k ∈ Finset.range n, p.coeff k * z ^ k :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => p.coeff k * z ^ k) n
    _ = p.eval z := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum]
      symm
      apply Finset.sum_subset
      · intro k hk
        exact Finset.mem_range.mpr ((Polynomial.le_natDegree_of_mem_supp _ hk).trans_lt hp)
      · intro k _ hk
        have hcoeff : p.coeff k = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hk
        rw [hcoeff, zero_mul]

theorem firstSheetKernelNumerator_natDegree_lt {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (firstSheetKernelNumerator x i).natDegree < n := by
  have hfactor (j : Fin n) : (1 - C (x j : ℂ) * (X : ℂ[X])).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  calc
    (firstSheetKernelNumerator x i).natDegree ≤
        ∑ j ∈ Finset.univ.erase i, (1 - C (x j : ℂ) * (X : ℂ[X])).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum (fun j _ => hfactor j)
    _ = n - 1 := by simp
    _ < n := by have hi := i.isLt; omega

theorem firstSheetKernelCoefficients_numerator {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (z : ℂ) :
    firstSheetNumerator (firstSheetKernelCoefficients x i) z =
      ∏ j ∈ Finset.univ.erase i, (1 - (x j : ℂ) * z) := by
  change firstSheetNumerator (fun k : Fin n => (firstSheetKernelNumerator x i).coeff (k : ℕ)) z = _
  rw [firstSheetNumerator_coefficients _ (firstSheetKernelNumerator_natDegree_lt x i)]
  simp only [firstSheetKernelNumerator, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]

theorem firstSheetRational_kernelCoefficients {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (i : Fin n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    firstSheetRational Finset.univ x (firstSheetKernelCoefficients x i) z =
      firstSheetKernel (x i) z := by
  have hden := firstSheetDenominator_ne_zero Finset.univ x (fun j _ => hx j) hz
  have hi := blaschkeFactor_denominator_ne_zero (hx i) hz
  have hp : (1 - (x i : ℂ) * z) *
      (∏ j ∈ Finset.univ.erase i, (1 - (x j : ℂ) * z)) = firstSheetDenominator Finset.univ x z :=
    Finset.mul_prod_erase Finset.univ (fun j => 1 - (x j : ℂ) * z) (Finset.mem_univ i)
  rw [firstSheetRational, firstSheetKernelCoefficients_numerator, firstSheetKernel]
  apply (div_eq_iff hden).mpr
  rw [← hp, ← mul_assoc, inv_mul_cancel₀ hi, one_mul]

end InternalCatalan

end



noncomputable section
open Complex MeasureTheory
open scoped BigOperators
namespace InternalCatalan

def firstSheetRationalBoundaryMap {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    (Fin n → ℂ) →ₗ[ℂ] C(Circle, ℂ) where
  toFun a := firstSheetBoundaryFunction (firstSheetRational Finset.univ x a)
    (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun i _ => hx i) a).continuousOn
  map_add' a b := by
    ext z
    change firstSheetRational Finset.univ x (a + b) (z : ℂ) =
      firstSheetRational Finset.univ x a (z : ℂ) + firstSheetRational Finset.univ x b (z : ℂ)
    simp only [firstSheetRational, firstSheetNumerator, Pi.add_apply, add_mul,
      Finset.sum_add_distrib, add_div]
  map_smul' c a := by
    ext z
    change firstSheetRational Finset.univ x (c • a) (z : ℂ) =
      c * firstSheetRational Finset.univ x a (z : ℂ)
    simp only [firstSheetRational, firstSheetNumerator, Pi.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum, mul_div_assoc]

def firstSheetRationalEmbedding {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    (Fin n → ℂ) →ₗ[ℂ] FirstSheetBoundaryL2 :=
  firstSheetBoundaryToLp.toLinearMap.comp (firstSheetRationalBoundaryMap x hx)

theorem firstSheetRationalEmbedding_apply {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (a : Fin n → ℂ) :
    firstSheetRationalEmbedding x hx a =
      firstSheetBoundaryVector (firstSheetRational Finset.univ x a)
        (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun i _ => hx i) a).continuousOn := rfl

theorem firstSheetRationalEmbedding_inner_kernel {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (a : Fin n → ℂ) (i : Fin n) :
    inner ℂ (firstSheetKernelVector (x i) (hx i)) (firstSheetRationalEmbedding x hx a) =
      firstSheetRational Finset.univ x a (x i : ℂ) := by
  rw [firstSheetRationalEmbedding_apply]
  exact firstSheetBoundary_inner_kernel
    (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun j _ => hx j) a) (hx i)

theorem firstSheetRationalEmbedding_injective {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) :
    Function.Injective (firstSheetRationalEmbedding x hx) := by
  intro a b hab
  apply (firstSheetEvaluationEquiv x hxi).injective
  ext i
  have hip := congrArg (fun v => inner ℂ (firstSheetKernelVector (x i) (hx i)) v) hab
  rw [firstSheetRationalEmbedding_inner_kernel, firstSheetRationalEmbedding_inner_kernel] at hip
  have heval := congrArg (fun w : ℂ => firstSheetDenominator Finset.univ x (x i : ℂ) * w) hip
  rw [← firstSheetEvaluation_eq_denominator_mul_value x hx a i,
    ← firstSheetEvaluation_eq_denominator_mul_value x hx b i] at heval
  simpa only [firstSheetEvaluationEquiv_apply, firstSheetEvaluation_apply] using heval

def firstSheetSpace {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    Submodule ℂ FirstSheetBoundaryL2 := (firstSheetRationalEmbedding x hx).range

instance firstSheetSpace_finiteDimensional {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    FiniteDimensional ℂ (firstSheetSpace x hx) := by
  unfold firstSheetSpace
  infer_instance

theorem firstSheetKernelVector_mem_space {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (i : Fin n) :
    firstSheetKernelVector (x i) (hx i) ∈ firstSheetSpace x hx := by
  refine ⟨firstSheetKernelCoefficients x i, ?_⟩
  rw [firstSheetRationalEmbedding_apply]
  unfold firstSheetKernelVector firstSheetBoundaryVector
  apply congrArg firstSheetBoundaryToLp
  ext z
  exact firstSheetRational_kernelCoefficients x hx i (by simp only [Circle.norm_coe, le_refl])

theorem firstSheetRationalEmbedding_norm_sq {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (a : Fin n → ℂ) :
    ‖firstSheetRationalEmbedding x hx a‖ ^ 2 = firstSheetBoundaryNormSq Finset.univ x a := by
  rw [firstSheetRationalEmbedding_apply]
  exact firstSheetBoundary_norm_sq_function _

theorem firstSheetRationalEmbedding_reverse_norm {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (a : Fin n → ℂ) :
    ‖firstSheetRationalEmbedding x hx (firstSheetReverse n a)‖ =
      ‖firstSheetRationalEmbedding x hx a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [firstSheetRationalEmbedding_norm_sq, firstSheetRationalEmbedding_norm_sq,
    firstSheetBoundaryNormSq_reverse]

def firstSheetProjection {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    FirstSheetBoundaryL2 →L[ℂ] FirstSheetBoundaryL2 :=
  (firstSheetSpace x hx).starProjection

theorem firstSheetProjection_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (u : FirstSheetBoundaryL2) :
    ‖firstSheetProjection x hx u‖ ≤ ‖u‖ :=
  (firstSheetSpace x hx).norm_starProjection_apply_le u

theorem firstSheetProjection_inner_kernel {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (u : FirstSheetBoundaryL2) (i : Fin n) :
    inner ℂ (firstSheetKernelVector (x i) (hx i)) (firstSheetProjection x hx u) =
      inner ℂ (firstSheetKernelVector (x i) (hx i)) u := by
  have h := inner_eq_zero_symm.mp ((firstSheetSpace x hx).starProjection_inner_eq_zero
    u (firstSheetKernelVector (x i) (hx i)) (firstSheetKernelVector_mem_space x hx i))
  rw [inner_sub_right, sub_eq_zero] at h
  exact h.symm

end InternalCatalan

end



noncomputable section
open Complex Metric
open scoped BigOperators
namespace InternalCatalan

theorem firstSheetBoundary_mul_norm_le {h u : ℂ → ℂ}
    (hh : ContinuousOn h (closedBall (0 : ℂ) 1))
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) :
    ‖firstSheetBoundaryVector (fun z => h z * u z) (hh.mul hu)‖ ≤
      K * ‖firstSheetBoundaryVector u hu‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  rw [mul_pow, firstSheetBoundary_norm_sq_function, firstSheetBoundary_norm_sq_function]
  have hcu := hu.norm.pow 2
  have hch := (hh.mul hu).norm.pow 2
  have hcr : ContinuousOn (fun z => K ^ 2 * ‖u z‖ ^ 2) (closedBall (0 : ℂ) 1) :=
    continuousOn_const.mul hcu
  calc
    Real.circleAverage (fun z => ‖h z * u z‖ ^ 2) 0 1 ≤
        Real.circleAverage (fun z => K ^ 2 * ‖u z‖ ^ 2) 0 1 := by
      apply Real.circleAverage_mono
        (ContinuousOn.circleIntegrable (by norm_num) (hch.mono sphere_subset_closedBall))
        (ContinuousOn.circleIntegrable (by norm_num) (hcr.mono sphere_subset_closedBall))
      intro z hz
      change ‖h z * u z‖ ^ 2 ≤ K ^ 2 * ‖u z‖ ^ 2
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hbound z (sphere_subset_closedBall (by simpa using hz))) 2)
        (sq_nonneg _)
    _ = K ^ 2 * Real.circleAverage (fun z => ‖u z‖ ^ 2) 0 1 := by
      simpa only [smul_eq_mul] using (Real.circleAverage_fun_smul
        (a := K ^ 2) (f := fun z : ℂ => ‖u z‖ ^ 2) (c := 0) (R := 1))

theorem firstSheetProjection_mul_eq {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedBall (0 : ℂ) 1)) (a : Fin n → ℂ) :
    firstSheetProjection x hx
      (firstSheetBoundaryVector (fun z => h z * firstSheetRational Finset.univ x a z)
        (hh.mul (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun i _ => hx i) a)).continuousOn) =
      firstSheetRationalEmbedding x hx (firstSheetInterpolatingMultiplier x hxi h a) := by
  let u : FirstSheetBoundaryL2 := firstSheetBoundaryVector
    (fun z => h z * firstSheetRational Finset.univ x a z)
    (hh.mul (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun i _ => hx i) a)).continuousOn
  have hmem : firstSheetProjection x hx u ∈ firstSheetSpace x hx :=
    (firstSheetSpace x hx).starProjection_apply_mem u
  obtain ⟨b, hb⟩ := hmem
  have hba : b = firstSheetInterpolatingMultiplier x hxi h a := by
    apply (firstSheetEvaluationEquiv x hxi).injective
    ext i
    rw [firstSheetEvaluationEquiv_apply, firstSheetEvaluationEquiv_apply,
      firstSheetInterpolatingMultiplier_eval]
    have hip := firstSheetProjection_inner_kernel x hx u i
    rw [← hb, firstSheetRationalEmbedding_inner_kernel] at hip
    have hrepro := firstSheetBoundary_inner_kernel
      (hh.mul (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun j _ => hx j) a)) (hx i)
    change inner ℂ (firstSheetKernelVector (x i) (hx i)) u =
      h (x i : ℂ) * firstSheetRational Finset.univ x a (x i : ℂ) at hrepro
    rw [hrepro] at hip
    have hden := firstSheetDenominator_ne_zero Finset.univ x (fun j _ => hx j)
      (show ‖(x i : ℂ)‖ ≤ 1 by simpa only [Complex.norm_real, Real.norm_eq_abs] using (hx i).le)
    unfold firstSheetRational at hip
    field_simp [hden] at hip
    exact hip
  rw [hba] at hb
  exact hb.symm

theorem firstSheetInterpolatingMultiplier_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) (a : Fin n → ℂ) :
    ‖firstSheetRationalEmbedding x hx (firstSheetInterpolatingMultiplier x hxi h a)‖ ≤
      K * ‖firstSheetRationalEmbedding x hx a‖ := by
  rw [← firstSheetProjection_mul_eq x hx hxi h hh a]
  refine (firstSheetProjection_norm_le x hx _).trans ?_
  rw [firstSheetRationalEmbedding_apply]
  exact firstSheetBoundary_mul_norm_le hh.continuousOn
    (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun i _ => hx i) a).continuousOn hK hbound

theorem firstSheetEvaluationOperator_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) (a : Fin n → ℂ) :
    ‖firstSheetRationalEmbedding x hx (firstSheetEvaluationOperator x hxi h a)‖ ≤
      (1 + K) * ‖firstSheetRationalEmbedding x hx a‖ := by
  change ‖firstSheetRationalEmbedding x hx
    (a + firstSheetInterpolatingMultiplier x hxi h (firstSheetReverse n a))‖ ≤ _
  rw [map_add]
  calc
    _ ≤ ‖firstSheetRationalEmbedding x hx a‖ +
        ‖firstSheetRationalEmbedding x hx (firstSheetInterpolatingMultiplier x hxi h (firstSheetReverse n a))‖ :=
      norm_add_le _ _
    _ ≤ ‖firstSheetRationalEmbedding x hx a‖ +
        K * ‖firstSheetRationalEmbedding x hx (firstSheetReverse n a)‖ :=
      add_le_add (le_refl _) (firstSheetInterpolatingMultiplier_norm_le x hx hxi h hh hK hbound _)
    _ = (1 + K) * ‖firstSheetRationalEmbedding x hx a‖ := by
      rw [firstSheetRationalEmbedding_reverse_norm]
      ring

end InternalCatalan

end



noncomputable section
namespace InternalCatalan

def firstSheetSpaceEquiv {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (hxi : Function.Injective x) : (Fin n → ℂ) ≃ₗ[ℂ] firstSheetSpace x hx :=
  LinearEquiv.ofInjective (firstSheetRationalEmbedding x hx)
    (firstSheetRationalEmbedding_injective x hx hxi)


theorem firstSheetSpace_finrank {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (hxi : Function.Injective x) : Module.finrank ℂ (firstSheetSpace x hx) = n := by
  rw [← (firstSheetSpaceEquiv x hx hxi).finrank_eq]
  simp

def firstSheetSpaceOperator {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (hxi : Function.Injective x) (h : ℂ → ℂ) :
    firstSheetSpace x hx →ₗ[ℂ] firstSheetSpace x hx :=
  (firstSheetSpaceEquiv x hx hxi).toLinearMap.comp
    ((firstSheetEvaluationOperator x hxi h).comp (firstSheetSpaceEquiv x hx hxi).symm.toLinearMap)

theorem firstSheetSpaceOperator_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) (u : firstSheetSpace x hx) :
    ‖firstSheetSpaceOperator x hx hxi h u‖ ≤ (1 + K) * ‖u‖ := by
  obtain ⟨a, rfl⟩ := (firstSheetSpaceEquiv x hx hxi).surjective u
  change ‖firstSheetSpaceEquiv x hx hxi
    (firstSheetEvaluationOperator x hxi h
      ((firstSheetSpaceEquiv x hx hxi).symm (firstSheetSpaceEquiv x hx hxi a)))‖ ≤ _
  rw [LinearEquiv.symm_apply_apply]
  change ‖firstSheetRationalEmbedding x hx (firstSheetEvaluationOperator x hxi h a)‖ ≤
    (1 + K) * ‖firstSheetRationalEmbedding x hx a‖
  exact firstSheetEvaluationOperator_norm_le x hx hxi h hh hK hbound a

theorem firstSheetSpaceOperator_det {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (hxi : Function.Injective x) (h : ℂ → ℂ) :
    LinearMap.det (firstSheetSpaceOperator x hx hxi h) =
      LinearMap.det (firstSheetEvaluationOperator x hxi h) :=
  LinearMap.det_conj _ (firstSheetSpaceEquiv x hx hxi)

end InternalCatalan




open scoped BigOperators
namespace InternalCatalan

theorem firstSheetMixedEvaluationMatrix_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) :
    ‖(firstSheetMixedEvaluationMatrix x h).det‖ ≤
      (1 + K) ^ n * ‖(Matrix.vandermonde (fun i => (x i : ℂ))).det‖ := by
  have hdet := firstSheet_det_norm_le_pow (firstSheetSpaceOperator x hx hxi h)
    (firstSheetSpaceOperator_norm_le x hx hxi h hh hK hbound)
  rw [firstSheetSpaceOperator_det, firstSheetSpace_finrank x hx hxi] at hdet
  rw [firstSheetMixedEvaluationMatrix_det x hxi, norm_mul, norm_mul,
    firstSheetReverse_det_norm, mul_one]
  calc
    _ ≤ ‖(Matrix.vandermonde (fun i => (x i : ℂ))).det‖ * (1 + K) ^ n :=
      mul_le_mul_of_nonneg_left hdet (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem firstSheet_uniform_mixed_determinant_bound {n D : ℕ} (x : Fin n → ℝ)
    (hn : 48 ≤ n) (hDpos : 0 < D) (hDn : D ≤ n)
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x)
    (hweight : (∑ i : Fin n, blaschkeWeight (x i)) ≤ (D : ℝ)) :
    ‖(Matrix.of (fun i k : Fin n =>
      (x i : ℂ) ^ (k.rev : ℕ) +
        (if x i < 0 then (x i : ℂ) ^ D else -5 * (x i : ℂ) ^ D) *
          (x i : ℂ) ^ (k : ℕ))).det‖ ≤
      (1 + 10 * Real.exp 12 * (n : ℝ)) ^ n *
        ‖(Matrix.vandermonde (fun i => (x i : ℂ))).det‖ := by
  obtain ⟨h, hh, heval, hbound⟩ := real_uniform_interpolation_actual Finset.univ x D n hn
    hDpos hDn (by simp) (fun i _ => hx0 i) (fun i _ => hx i) hweight
  have hm : firstSheetMixedEvaluationMatrix x h = Matrix.of (fun i k : Fin n =>
      (x i : ℂ) ^ (k.rev : ℕ) +
        (if x i < 0 then (x i : ℂ) ^ D else -5 * (x i : ℂ) ^ D) *
          (x i : ℂ) ^ (k : ℕ)) := by
    ext i k
    simp only [firstSheetMixedEvaluationMatrix, Matrix.of_apply, heval i (Finset.mem_univ i)]
  rw [← hm]
  exact firstSheetMixedEvaluationMatrix_norm_le x hx hxi h hh (by positivity) hbound

end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan

theorem firstSheet_norm_ofReal_det {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    ‖(M.map Complex.ofReal).det‖ = |M.det| := by
  calc
    _ = ‖(M.det : ℂ)‖ := congrArg norm (Complex.ofRealHom.map_det M).symm
    _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]

theorem firstSheet_uniform_real_mixed_determinant_bound {m D : ℕ} (x : Fin m → ℝ)
    (hm : 48 ≤ m) (hDpos : 0 < D) (hDm : D ≤ m)
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x)
    (hweight : (∑ i : Fin m, blaschkeWeight (x i)) ≤ (D : ℝ)) :
    |(Matrix.of (fun r i : Fin m => x i ^ (r.rev : ℕ) +
      (if x i < 0 then x i ^ D else -5 * x i ^ D) * x i ^ (r : ℕ))).det| ≤
      (1 + 10 * Real.exp 12 * (m : ℝ)) ^ m * |(Matrix.vandermonde x).det| := by
  let M : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun r i => x i ^ (r.rev : ℕ) +
    (if x i < 0 then x i ^ D else -5 * x i ^ D) * x i ^ (r : ℕ))
  have hmap : Matrix.of (fun i k : Fin m =>
      (x i : ℂ) ^ (k.rev : ℕ) +
        (if x i < 0 then (x i : ℂ) ^ D else -5 * (x i : ℂ) ^ D) * (x i : ℂ) ^ (k : ℕ)) =
      (M.map Complex.ofReal).transpose := by
    ext i k
    by_cases hi : x i < 0 <;> simp [M, hi]
  have hv : Matrix.vandermonde (fun i => (x i : ℂ)) =
      (Matrix.vandermonde x).map Complex.ofReal := by
    ext i k
    simp [Matrix.vandermonde_apply]
  have hb := firstSheet_uniform_mixed_determinant_bound x hm hDpos hDm hx0 hx hxi hweight
  rw [hmap, Matrix.det_transpose, hv, firstSheet_norm_ofReal_det, firstSheet_norm_ofReal_det] at hb
  exact hb

theorem firstSheet_laurent_vandermonde_weight {m : ℕ} (g : ℕ) (x : Fin m → ℝ)
    (hx0 : ∀ i, x i ≠ 0) :
    (∏ i : Fin m, |x i ^ ((g : ℤ) - ((m - 1 : ℕ) : ℤ))|) *
        |(Matrix.vandermonde x).det| =
      |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
        ∏ i : Fin m, |x i| ^ g := by
  have hp (i : Fin m) : |x i ^ ((g : ℤ) - ((m - 1 : ℕ) : ℤ))| =
      |x i| ^ g / |x i| ^ (m - 1) := by
    rw [abs_zpow, zpow_sub₀ (abs_ne_zero.mpr (hx0 i)), zpow_natCast, zpow_natCast]
  simp only [hp, Finset.prod_div_distrib]
  rw [Matrix.det_vandermonde, abs_vandermonde_inv x hx0]
  ring

end InternalCatalan

end



noncomputable section
open Set
open scoped BigOperators
namespace InternalCatalan

theorem realSheetDeterminant_first_sheet_bound {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x)
    (hcase : (∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
      ((n N - 1 - 2 * g N : ℕ) : ℝ)) :
    |realSheetDeterminant N x| ≤
      (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
          ∏ i : Fin (n N), |x i| ^ g N := by
  have hn : 48 ≤ n N := by unfold n; omega
  have hDpos : 0 < n N - 1 - 2 * g N := by unfold n g; omega
  have hDn : n N - 1 - 2 * g N ≤ n N := by omega
  have hxabs : ∀ i, |x i| < 1 := fun i => abs_lt.mpr (hx i)
  have hweight : (∑ i : Fin (n N), blaschkeWeight (x i)) ≤
      ((n N - 1 - 2 * g N : ℕ) : ℝ) := by
    simpa only [blaschkeWeight] using hcase
  have hmixed : |(realFirstSheetMixedMatrix N x).det| ≤
      (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N * |(Matrix.vandermonde x).det| :=
    firstSheet_uniform_real_mixed_determinant_bound x hn hDpos hDn hx0 hxabs hxi hweight
  have hprod : 0 ≤ ∏ i : Fin (n N), |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) :=
    Finset.prod_nonneg (fun i _ => zpow_nonneg (abs_nonneg (x i)) _)
  have hw : (∏ i : Fin (n N), |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
      |(Matrix.vandermonde x).det| =
      |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
        ∏ i : Fin (n N), |x i| ^ g N := by
    simpa only [abs_zpow] using firstSheet_laurent_vandermonde_weight (g N) x hx0
  calc
    |realSheetDeterminant N x| ≤
        (∏ i : Fin (n N), |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
          |(realFirstSheetMixedMatrix N x).det| :=
      realSheetDeterminant_abs_le_firstSheet_mixed hN x hx0
    _ ≤ (∏ i : Fin (n N), |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
        ((1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N * |(Matrix.vandermonde x).det|) :=
      mul_le_mul_of_nonneg_left hmixed hprod
    _ = (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N *
        ((∏ i : Fin (n N), |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
          |(Matrix.vandermonde x).det|) := by ring
    _ = _ := by rw [hw]; ring

end InternalCatalan

end



noncomputable section
open Set
open scoped BigOperators

namespace InternalCatalan

theorem abs_sheetRealIntegrand_le_majorantTwo {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hcase : (∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
      ((n N - 1 - 2 * g N : ℕ) : ℝ)) :
    |sheetRealIntegrand N x s| ≤
      (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N * realEnergyMajorantTwo N x s := by
  rw [abs_sheetRealIntegrand_eq N x s hx hs]
  calc
    _ ≤ ((1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
        (∏ i : Fin (n N), |x i| ^ g N)) * realPrincipalIntegrand N x s :=
      mul_le_mul_of_nonneg_right (realSheetDeterminant_first_sheet_bound hN x hx hx0 hxi hcase)
        (realPrincipalIntegrand_nonneg N x s hx hs)
    _ = _ := by unfold realEnergyMajorantTwo; ring

end InternalCatalan

end



noncomputable section
open Set
open scoped BigOperators

namespace InternalCatalan

theorem abs_determinant_le_of_two_majorant_bounds {N : ℕ} (hN : 0 < N)
    {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hbound₁ : ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) →
      realEnergyMajorantOne N x s ≤ M₁)
    (hbound₂ : ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      ((∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
        ((n N - 1 - 2 * g N : ℕ) : ℝ)) →
      realEnergyMajorantTwo N x s ≤ M₂) :
    |determinant N| ≤
      ((2 : ℝ) ^ n N *
        max ((1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N)
          ((3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2)) /
        (((n N).factorial : ℝ) ^ 2)) * max M₁ M₂ := by
  let K₁ : ℝ := (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N
  let K₂ : ℝ := (3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2)
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (Nat.cast_nonneg (n N)) _)
  have hK : 0 ≤ max K₁ K₂ := hK₁.trans (le_max_left _ _)
  have hM : 0 ≤ max M₁ M₂ := hM₁.trans (le_max_left _ _)
  have hsheet : ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      |sheetRealIntegrand N x s| ≤ max K₁ K₂ * max M₁ M₂ := by
    intro x s hx hs hx0 hxi hsi
    by_cases hcase : (∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
        ((n N - 1 - 2 * g N : ℕ) : ℝ)
    · calc
        _ ≤ K₁ * realEnergyMajorantTwo N x s :=
          abs_sheetRealIntegrand_le_majorantTwo hN x s hx hx0 hxi hs hcase
        _ ≤ K₁ * M₂ :=
          mul_le_mul_of_nonneg_left (hbound₂ x s hx hs hx0 hxi hsi hcase) hK₁
        _ ≤ max K₁ K₂ * max M₁ M₂ :=
          mul_le_mul (le_max_left _ _) (le_max_right _ _) hM₂ hK
    · calc
        _ ≤ K₂ * realEnergyMajorantOne N x s :=
          abs_sheetRealIntegrand_le_majorantOne hN x s hx hx0 hs
        _ ≤ K₂ * M₁ :=
          mul_le_mul_of_nonneg_left (hbound₁ x s hx hs hx0 hxi hsi (lt_of_not_ge hcase)) hK₂
        _ ≤ max K₁ K₂ * max M₁ M₂ :=
          mul_le_mul (le_max_right _ _) (le_max_left _ _) hM₁ hK
  have hi := abs_determinant_le_of_sheetRealIntegrand_bound hN (mul_nonneg hK hM) hsheet
  apply hi.trans_eq
  dsimp [K₁, K₂]
  ring

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTailPairRational
namespace OAI

noncomputable section

namespace InternalCatalan













theorem barrier_finite_lengths :
    barrierP2Finite.length = 10 ∧ barrierV2Finite.length = 10 ∧
    barrierP1Finite.length = 8 ∧ barrierV1Finite.length = 8 := by decide

theorem barrier_tail_lengths : barrierP2Tail.length = 10 ∧ barrierV2Tail.length = 13 := by
  norm_num [barrierP2Tail, barrierV2Tail, barrierConjugatePair]

theorem barrier_lambdas : barrierLambda2 = 0 ∧ 0 ≤ barrierLambda1 ∧
    barrierLambda1 < 5 / 2 := by
  norm_num [barrierLambda1, barrierLambda2]

theorem barrierP2_finite_abs_lt_one :
    ∀ a ∈ barrierP2Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierP2Finite]

theorem barrierV2_finite_abs_lt_one :
    ∀ a ∈ barrierV2Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierV2Finite]

theorem barrierP1_finite_abs_lt_one :
    ∀ a ∈ barrierP1Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierP1Finite]

theorem barrierV1_finite_abs_lt_one :
    ∀ a ∈ barrierV1Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierV1Finite]

theorem barrierP2_tail_norm_bounds :
    ∀ zr ∈ barrierP2Tail, ‖zr.1‖ ≤ (94 / 100 : ℝ) ∧ ‖zr.2‖ < 1 := by
  have hs : ∀ zr ∈ barrierP2Tail,
      Complex.normSq zr.1 ≤ (94 / 100 : ℝ) ^ 2 ∧ Complex.normSq zr.2 < 1 := by
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex,
      Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]
  intro zr hzr
  obtain ⟨hb, hr⟩ := hs zr hzr
  rw [Complex.normSq_eq_norm_sq] at hb hr
  constructor
  · nlinarith only [hb, norm_nonneg zr.1]
  · nlinarith only [hr, norm_nonneg zr.2]

theorem barrierV2_tail_norm_bounds :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ ≤ (984 / 1000 : ℝ) ∧ ‖zr.2‖ < 1 := by
  have hs : ∀ zr ∈ barrierV2Tail,
      Complex.normSq zr.1 ≤ (984 / 1000 : ℝ) ^ 2 ∧ Complex.normSq zr.2 < 1 := by
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex,
      Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]
  intro zr hzr
  obtain ⟨hb, hr⟩ := hs zr hzr
  rw [Complex.normSq_eq_norm_sq] at hb hr
  constructor
  · nlinarith only [hb, norm_nonneg zr.1]
  · nlinarith only [hr, norm_nonneg zr.2]

theorem barrierFiniteCoeff_abs_le (cs : List ℤ) (hlen : cs.length ≤ 10)
    (hcoeff : ∀ a ∈ cs, |(a : ℝ) / 100000000| < 1) (k : ℕ) :
    |barrierFiniteCoeff cs k| ≤ 2 * (99 / 100 : ℝ) ^ k := by
  by_cases hk : k = 0
  · subst k
    norm_num [barrierFiniteCoeff]
  rw [barrierFiniteCoeff, if_neg hk]
  by_cases hi : k - 1 < cs.length
  · have hmem : cs.getD (k - 1) 0 ∈ cs := by
      rw [List.getD_eq_getElem cs 0 hi]
      exact List.getElem_mem hi
    have hk10 : k ≤ 10 := by omega
    have hpow : (99 / 100 : ℝ) ^ 10 ≤ (99 / 100 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk10
    calc
      |(cs.getD (k - 1) 0 : ℝ) / 100000000| ≤ 1 :=
        le_of_lt (hcoeff _ hmem)
      _ ≤ 2 * (99 / 100 : ℝ) ^ 10 := by norm_num
      _ ≤ 2 * (99 / 100 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
  · rw [List.getD_eq_default cs 0 (Nat.le_of_not_gt hi)]
    simp only [Int.cast_zero, zero_div, abs_zero]
    exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)


































open Polynomial
















end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierFinitePotentialRat
namespace OAI

noncomputable section

namespace InternalCatalan

section

private theorem barrierTail_norm_le (tail : List (ℂ × ℂ)) (k : ℕ) :
    (∀ zr ∈ tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1) →
      ‖(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum‖ ≤
        (tail.length : ℝ) * (99 / 100 : ℝ) ^ k := by
  induction tail with
  | nil => simp
  | cons zr tail ih =>
    intro hb
    have hz := hb zr (List.mem_cons_self)
    have ht := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    have hone : ‖zr.2 * zr.1 ^ k‖ ≤ (99 / 100 : ℝ) ^ k := by
      rw [norm_mul, norm_pow]
      calc
        _ ≤ 1 * (99 / 100 : ℝ) ^ k := by
          gcongr
          · exact hz.2
          · exact hz.1
        _ = _ := one_mul _
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ‖zr.2 * zr.1 ^ k‖ + ‖(tail.map (fun w : ℂ × ℂ => w.2 * w.1 ^ k)).sum‖ :=
        norm_add_le _ _
      _ ≤ (99 / 100 : ℝ) ^ k + (tail.length : ℝ) * (99 / 100 : ℝ) ^ k :=
        add_le_add hone ht
      _ = _ := by ring

private theorem barrierTrial_abs_le (cs : List ℤ) (tail : List (ℂ × ℂ))
    (hc : cs.length ≤ 10)
    (ha : ∀ a ∈ cs, |(a : ℝ) / 100000000| < 1)
    (ht : tail.length ≤ 13)
    (hb : ∀ zr ∈ tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1) (k : ℕ) :
    |barrierTrial cs tail k| ≤ 15 * (99 / 100 : ℝ) ^ k := by
  by_cases hk : k = 0
  · simp [barrierTrial, hk]
  have htail : |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| ≤
      13 * (99 / 100 : ℝ) ^ k := by
    exact (Complex.abs_re_le_norm _).trans ((barrierTail_norm_le tail k hb).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (by positivity)))
  simp only [barrierTrial, if_neg hk]
  calc
    _ ≤ |barrierFiniteCoeff cs k| +
        |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (barrierFiniteCoeff cs k)
        ((tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re)
    _ ≤ 2 * (99 / 100 : ℝ) ^ k + 13 * (99 / 100 : ℝ) ^ k :=
      add_le_add (barrierFiniteCoeff_abs_le cs hc ha k) htail
    _ = _ := by ring

theorem barrier_trials_abs_le (k : ℕ) :
    |barrierP2 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierV2 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierP1 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierV1 k| ≤ 15 * (99 / 100 : ℝ) ^ k := by
  have hp : ∀ zr ∈ barrierP2Tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1 := by
    intro zr hz
    have h := barrierP2_tail_norm_bounds zr hz
    exact ⟨h.1.trans (by norm_num), h.2.le⟩
  have hv : ∀ zr ∈ barrierV2Tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1 := by
    intro zr hz
    have h := barrierV2_tail_norm_bounds zr hz
    exact ⟨h.1.trans (by norm_num), h.2.le⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact barrierTrial_abs_le barrierP2Finite barrierP2Tail
      barrier_finite_lengths.1.le barrierP2_finite_abs_lt_one
      (barrier_tail_lengths.1.le.trans (by norm_num)) hp k
  · exact barrierTrial_abs_le barrierV2Finite barrierV2Tail
      barrier_finite_lengths.2.1.le barrierV2_finite_abs_lt_one
      barrier_tail_lengths.2.le hv k
  · exact barrierTrial_abs_le barrierP1Finite []
      (barrier_finite_lengths.2.2.1.le.trans (by norm_num)) barrierP1_finite_abs_lt_one
      (by simp) (by simp) k
  · exact barrierTrial_abs_le barrierV1Finite []
      (barrier_finite_lengths.2.2.2.le.trans (by norm_num)) barrierV1_finite_abs_lt_one
      (by simp) (by simp) k

theorem barrier_trials_abs_summable :
    Summable (fun k => |barrierP2 k|) ∧ Summable (fun k => |barrierV2 k|) ∧
    Summable (fun k => |barrierP1 k|) ∧ Summable (fun k => |barrierV1 k|) := by
  have hg : Summable (fun k : ℕ => (15 : ℝ) * (99 / 100 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(99 / 100 : ℝ)‖ < 1)).mul_left 15
  refine ⟨hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.2.1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.2.2)⟩





open Polynomial Filter
open scoped BigOperators



private theorem barrierTrialT_term_norm_le (u : ℕ → ℝ) (k : ℕ) {x : ℝ}
    (hx : |x| ≤ 1) :
    ‖u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
      ((k + 1 : ℕ) : ℝ)‖ ≤ |u (k + 1)| := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have ht := Chebyshev.abs_eval_T_real_le_one ((k + 1 : ℕ) : ℤ) hx
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| * 1 / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg _)) hkp.le
    _ = |u (k + 1)| / ((k + 1 : ℕ) : ℝ) := by rw [mul_one]
    _ ≤ |u (k + 1)| := div_le_self (abs_nonneg _) hk

private theorem barrierTrialS_term_norm_le (u : ℕ → ℝ) (k : ℕ) {x : ℝ}
    (hx : |x| ≤ 1) :
    ‖u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)‖ ≤ |u (k + 1)| := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have ht : |x| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_pow, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| * 1 / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg _)) hkp.le
    _ = |u (k + 1)| / ((k + 1 : ℕ) : ℝ) := by rw [mul_one]
    _ ≤ |u (k + 1)| := div_le_self (abs_nonneg _) hk

theorem barrierTrialT_summable (u : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k : ℕ => u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
      ((k + 1 : ℕ) : ℝ)) := by
  exact ((summable_nat_add_iff 1).mpr hu).of_norm_bounded
    (fun k => barrierTrialT_term_norm_le u k hx)

theorem barrierTrialS_summable (u : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k : ℕ => u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  exact ((summable_nat_add_iff 1).mpr hu).of_norm_bounded
    (fun k => barrierTrialS_term_norm_le u k hx)




end

section

open scoped BigOperators





end
section

open Polynomial
open scoped BigOperators



end

section

open Polynomial Set Filter
open scoped BigOperators



end

open Polynomial







open Polynomial
open scoped BigOperators





end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealEnergyTrialDamping
namespace OAI

noncomputable section
open Polynomial Set
open scoped BigOperators

namespace InternalCatalan

def realEnergyTrialTau (u : ℕ → ℝ) (e x : ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) * realEnergyTau e ^ (k + 1) *
    (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)

def realEnergyTrialRho (u : ℕ → ℝ) (e x : ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) * realEnergyRho e x ^ (k + 1) * x ^ (k + 1) /
    ((k + 1 : ℕ) : ℝ)

def realEnergyTrialSigma (u : ℕ → ℝ) (e s : ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) * realEnergySigma e s ^ (k + 1) *
    (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval s / ((k + 1 : ℕ) : ℝ)

theorem energy_one_sub_pow_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (m : ℕ) :
    1 - r ^ m ≤ (m : ℝ) * (1 - r) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hp : r ^ m ≤ 1 := pow_le_one₀ hr.1 hr.2
      have hm := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hr.2)
      simp only [pow_succ, Nat.cast_succ]
      nlinarith only [ih, hm]

private theorem energy_trial_term_norm_le (a b : ℝ) {m : ℕ}
    (hm : 0 < m) (hb : |b| ≤ 1) : ‖a * b / (m : ℝ)‖ ≤ |a| := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_pos hm0]
  calc
    _ ≤ |a| * 1 / (m : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (abs_nonneg a)) hm0.le
    _ = |a| / (m : ℝ) := by rw [mul_one]
    _ ≤ |a| := div_le_self (abs_nonneg a) hm1

theorem energy_trial_damping_term_norm_le (a b : ℝ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (hb : |b| ≤ 1) :
    ‖a * r ^ m * b / (m : ℝ) - a * b / (m : ℝ)‖ ≤ (1 - r) * |a| := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hp0 : 0 ≤ 1 - r ^ m := sub_nonneg.mpr (pow_le_one₀ hr.1 hr.2)
  have hpdiv : (1 - r ^ m) / (m : ℝ) ≤ 1 - r := by
    apply (div_le_iff₀ hm0).mpr
    simpa only [mul_comm] using energy_one_sub_pow_le hr m
  have hfactor : a * r ^ m * b / (m : ℝ) - a * b / (m : ℝ) =
      -a * (1 - r ^ m) * b / (m : ℝ) := by ring
  rw [hfactor]
  simp only [norm_div, norm_mul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg hp0, abs_of_pos hm0]
  calc
    _ ≤ |a| * (1 - r ^ m) * 1 / (m : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg a) hp0)) hm0.le
    _ = |a| * ((1 - r ^ m) / (m : ℝ)) := by ring
    _ ≤ |a| * (1 - r) := mul_le_mul_of_nonneg_left hpdiv (abs_nonneg a)
    _ = (1 - r) * |a| := mul_comm _ _

theorem energy_damped_trial_summable (u v : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) (hv : ∀ k, |v k| ≤ 1)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    Summable (fun k : ℕ => u (k + 1) * r ^ (k + 1) * v (k + 1) /
      ((k + 1 : ℕ) : ℝ)) := by
  apply ((summable_nat_add_iff 1).mpr hu).of_norm_bounded
  intro k
  have hb : |r ^ (k + 1) * v (k + 1)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr.1 _)]
    have hp : r ^ (k + 1) ≤ 1 := pow_le_one₀ hr.1 hr.2
    exact (mul_le_mul hp (hv (k + 1))
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  simpa only [mul_assoc] using
    energy_trial_term_norm_le (u (k + 1)) (r ^ (k + 1) * v (k + 1))
      (Nat.succ_pos k) hb

theorem energy_damped_trial_sub_le (u v : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) (hv : ∀ k, |v k| ≤ 1)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    |(∑' k : ℕ, u (k + 1) * r ^ (k + 1) * v (k + 1) /
        ((k + 1 : ℕ) : ℝ)) -
      (∑' k : ℕ, u (k + 1) * v (k + 1) / ((k + 1 : ℕ) : ℝ))| ≤
      (1 - r) * (∑' k : ℕ, |u k|) := by
  have hud : Summable (fun k : ℕ => |u (k + 1)|) :=
    (summable_nat_add_iff 1).mpr hu
  have hbase : Summable (fun k : ℕ => u (k + 1) * v (k + 1) /
      ((k + 1 : ℕ) : ℝ)) := by
    simpa only [one_pow, mul_one] using
      energy_damped_trial_summable u v hu hv (r := 1) ⟨by norm_num, le_rfl⟩
  have hdamped := energy_damped_trial_summable u v hu hv hr
  have hdiff := hdamped.hasSum.sub hbase.hasSum
  have hbound := hdiff.norm_le_of_bounded (hud.hasSum.mul_left (1 - r))
    (fun k => energy_trial_damping_term_norm_le (u (k + 1)) (v (k + 1))
      hr (Nat.succ_pos k) (hv (k + 1)))
  have htail : (∑' k : ℕ, |u (k + 1)|) ≤ ∑' k : ℕ, |u k| := by
    have hsplit := hu.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at hsplit
    linarith [abs_nonneg (u 0)]
  simpa only [Real.norm_eq_abs] using hbound.trans
    (mul_le_mul_of_nonneg_left htail (sub_nonneg.mpr hr.2))

theorem realEnergyTrialTau_summable (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Summable (fun k : ℕ => u (k + 1) * realEnergyTau e ^ (k + 1) *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) := by
  have hr := realEnergyTau_bounds he
  exact energy_damped_trial_summable u (fun k => (Chebyshev.T ℝ (k : ℤ)).eval x)
    hu (fun k => Chebyshev.abs_eval_T_real_le_one (k : ℤ) (abs_lt.mpr hx).le)
    ⟨hr.1.le, hr.2.le⟩

theorem realEnergyTrialRho_summable (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Summable (fun k : ℕ => u (k + 1) * realEnergyRho e x ^ (k + 1) * x ^ (k + 1) /
      ((k + 1 : ℕ) : ℝ)) := by
  have hr := realEnergyRho_mem he hx
  exact energy_damped_trial_summable u (fun k => x ^ k) hu
    (fun k => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) (abs_lt.mpr hx).le)
    ⟨hr.1.le, hr.2.le⟩

theorem realEnergyTrialSigma_summable (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    Summable (fun k : ℕ => u (k + 1) * realEnergySigma e s ^ (k + 1) *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval s / ((k + 1 : ℕ) : ℝ)) := by
  have hr := realEnergySigma_mem he hs
  have hsabs : |s| ≤ 1 := by rw [abs_of_pos hs.1]; exact hs.2.le
  exact energy_damped_trial_summable u (fun k => (Chebyshev.T ℝ (k : ℤ)).eval s)
    hu (fun k => Chebyshev.abs_eval_T_real_le_one (k : ℤ) hsabs)
    ⟨hr.1.le, hr.2.le⟩

theorem realEnergyTrialTau_sub_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    |realEnergyTrialTau u e x - barrierTrialT u x| ≤ e * (∑' k : ℕ, |u k|) := by
  have hr := realEnergyTau_bounds he
  have hh := energy_damped_trial_sub_le u (fun k => (Chebyshev.T ℝ (k : ℤ)).eval x)
    hu (fun k => Chebyshev.abs_eval_T_real_le_one (k : ℤ) (abs_lt.mpr hx).le)
    (r := realEnergyTau e) ⟨hr.1.le, hr.2.le⟩
  change |realEnergyTrialTau u e x - barrierTrialT u x| ≤
    (1 - realEnergyTau e) * (∑' k : ℕ, |u k|) at hh
  have heq : 1 - realEnergyTau e = e := by unfold realEnergyTau; ring
  simpa only [heq] using hh

theorem realEnergyTrialRho_sub_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    |realEnergyTrialRho u e x - barrierTrialS u x| ≤
      (2 * e) * (∑' k : ℕ, |u k|) := by
  have hr := realEnergyRho_mem he hx
  have hh := energy_damped_trial_sub_le u (fun k => x ^ k) hu
    (fun k => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) (abs_lt.mpr hx).le)
    (r := realEnergyRho e x) ⟨hr.1.le, hr.2.le⟩
  change |realEnergyTrialRho u e x - barrierTrialS u x| ≤
    (1 - realEnergyRho e x) * (∑' k : ℕ, |u k|) at hh
  have herr : 1 - realEnergyRho e x ≤ 2 * e := by
    linarith [(realEnergyRho_bounds he hx).1]
  exact hh.trans (mul_le_mul_of_nonneg_right herr (tsum_nonneg (fun k => abs_nonneg (u k))))

theorem realEnergyTrialSigma_sub_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    |realEnergyTrialSigma u e s - barrierTrialT u s| ≤ e * (∑' k : ℕ, |u k|) := by
  have hr := realEnergySigma_mem he hs
  have hsabs : |s| ≤ 1 := by rw [abs_of_pos hs.1]; exact hs.2.le
  have hh := energy_damped_trial_sub_le u (fun k => (Chebyshev.T ℝ (k : ℤ)).eval s)
    hu (fun k => Chebyshev.abs_eval_T_real_le_one (k : ℤ) hsabs)
    (r := realEnergySigma e s) ⟨hr.1.le, hr.2.le⟩
  change |realEnergyTrialSigma u e s - barrierTrialT u s| ≤
    (1 - realEnergySigma e s) * (∑' k : ℕ, |u k|) at hh
  have herr : 1 - realEnergySigma e s ≤ e := by
    linarith [(realEnergySigma_bounds he hs).1]
  exact hh.trans (mul_le_mul_of_nonneg_right herr (tsum_nonneg (fun k => abs_nonneg (u k))))

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealEnergyDampedDual
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial Set
open scoped BigOperators

def realEnergyCosineMoment (N : ℕ) (e : ℝ) (x : Fin (n N) → ℝ) (k : ℕ) : ℝ :=
  (∑ i, realEnergyTau e ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (x i)) / (n N : ℝ)

def realEnergyPowerMoment (N : ℕ) (e : ℝ) (x : Fin (n N) → ℝ) (k : ℕ) : ℝ :=
  (∑ i, realEnergyRho e (x i) ^ k * x i ^ k) / (n N : ℝ)

def realEnergyColumnMoment (N : ℕ) (e : ℝ) (s : Fin (n N) → ℝ) (k : ℕ) : ℝ :=
  (∑ j, realEnergySigma e (s j) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s j)) /
    (n N : ℝ)

theorem energy_sum_sum_mul_div {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (c d : ℝ) :
    (∑ i, ∑ j, c * a i * b j / d) = c * (∑ i, a i) * (∑ j, b j) / d := by
  calc
    _ = ∑ i, (c * a i) * (∑ j, b j) / d := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_div, ← Finset.mul_sum]
    _ = (∑ i, c * a i) * (∑ j, b j) / d := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
    _ = _ := by rw [← Finset.mul_sum]

theorem energy_cosineMoment_square_div_eq (N : ℕ) (e : ℝ)
    (x : Fin (n N) → ℝ) (k : ℕ) :
    realEnergyCosineMoment N e x k ^ 2 / (k : ℝ) =
      (1 / (2 * (n N : ℝ) ^ 2)) *
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          2 * (realEnergyTau e ^ 2) ^ k *
            (Chebyshev.T ℝ (k : ℤ)).eval (x i) *
            (Chebyshev.T ℝ (k : ℤ)).eval (x j) / (k : ℝ)) := by
  unfold realEnergyCosineMoment
  rw [← Finset.mul_sum, energy_sum_sum_mul_div]
  simp only [pow_two, mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

theorem energy_hasSum_first_square {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => realEnergyCosineMoment N e x k ^ 2 / (k : ℝ))
      (-((∑ i : Fin (n N), ∑ j : Fin (n N),
            realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) /
          (n N : ℝ) ^ 2 + Real.log 2) / 2) := by
  have ht := realEnergyTau_bounds he
  have hr : realEnergyTau e ^ 2 ∈ Ico (0 : ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    have hm := mul_lt_mul_of_pos_left ht.2 ht.1
    nlinarith [ht.2]
  have hn : (n N : ℝ) ≠ 0 := by
    have hnpos : 0 < n N := by unfold n; omega
    exact (Nat.cast_pos.mpr hnpos).ne'
  have hseries :
      HasSum (fun k : ℕ => ∑ i : Fin (n N), ∑ j : Fin (n N),
          2 * (realEnergyTau e ^ 2) ^ k *
            (Chebyshev.T ℝ (k : ℤ)).eval (x i) *
            (Chebyshev.T ℝ (k : ℤ)).eval (x j) / (k : ℝ))
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          (-realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j) -
            Real.log 2)) := by
    apply hasSum_sum
    intro i hi
    apply hasSum_sum
    intro j hj
    exact energy_hasSum_cosine_kernel hr
      ⟨(hx i).1.le, (hx i).2.le⟩ ⟨(hx j).1.le, (hx j).2.le⟩
  convert hseries.mul_left (1 / (2 * (n N : ℝ) ^ 2)) using 1
  · rfl
  · funext k
    exact energy_cosineMoment_square_div_eq N e x k
  · simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn]
    ring


end

section

open Set
open scoped BigOperators

theorem energy_abs_average_le_one {m : ℕ} (hm : 0 < m)
    (a : Fin m → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |(∑ i, a i) / (m : ℝ)| ≤ 1 := by
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [abs_div, abs_of_pos hmp]
  apply (div_le_iff₀ hmp).mpr
  calc
    |∑ i, a i| ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => ha i)
    _ = 1 * (m : ℝ) := by simp

theorem energy_cosineMoment_abs_le_one {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (k : ℕ) :
    |realEnergyCosineMoment N e x k| ≤ 1 := by
  have hn : 0 < n N := by unfold n; omega
  apply energy_abs_average_le_one hn
  intro i
  have ht := realEnergyTau_bounds he
  rw [abs_mul, abs_pow, abs_of_pos ht.1]
  exact (mul_le_mul (pow_le_one₀ ht.1.le ht.2.le)
    (energy_chebyshev_abs_le_one k ⟨(hx i).1.le, (hx i).2.le⟩)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem energy_powerMoment_abs_le_one {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (k : ℕ) :
    |realEnergyPowerMoment N e x k| ≤ 1 := by
  have hn : 0 < n N := by unfold n; omega
  apply energy_abs_average_le_one hn
  intro i
  have hr := realEnergyRho_mem he (hx i)
  rw [abs_mul, abs_pow, abs_pow, abs_of_pos hr.1]
  exact (mul_le_mul (pow_le_one₀ hr.1.le hr.2.le)
    (pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨(hx i).1.le, (hx i).2.le⟩))
    (pow_nonneg (abs_nonneg _) _) (by norm_num)).trans_eq (one_mul _)

theorem energy_columnMoment_abs_le_one {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {s : Fin (n N) → ℝ} (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    |realEnergyColumnMoment N e s k| ≤ 1 := by
  have hn : 0 < n N := by unfold n; omega
  apply energy_abs_average_le_one hn
  intro j
  have hr := realEnergySigma_mem he (hs j)
  rw [abs_mul, abs_pow, abs_of_pos hr.1]
  exact (mul_le_mul (pow_le_one₀ hr.1.le hr.2.le)
    (energy_chebyshev_abs_le_one k ⟨by linarith [(hs j).1], (hs j).2.le⟩)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem energy_secondMoment_abs_le_three {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    |realEnergyPowerMoment N e x k - 2 * realEnergyColumnMoment N e s k| ≤ 3 := by
  have hb := energy_powerMoment_abs_le_one hN he hx k
  have hc := energy_columnMoment_abs_le_one hN he hs k
  calc
    _ ≤ |realEnergyPowerMoment N e x k| + |2 * realEnergyColumnMoment N e s k| :=
      abs_sub _ _
    _ = |realEnergyPowerMoment N e x k| + 2 * |realEnergyColumnMoment N e s k| := by
      rw [abs_mul]; norm_num
    _ ≤ 3 := by linarith

theorem energy_trial_norm_summable (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    Summable (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  have ht : Summable (fun k : ℕ => |u (k + 1)|) := (summable_nat_add_iff 1).mpr hu
  apply (ht.mul_left (∑' k, |u k|)).of_norm_bounded
  intro k
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have hb : |u (k + 1)| ≤ ∑' j, |u j| := hu.le_tsum (k + 1) (fun j _ => abs_nonneg _)
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| ^ 2 := div_le_self (sq_nonneg _) hk
    _ ≤ (∑' j, |u j|) * |u (k + 1)| := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hb (abs_nonneg (u (k + 1)))

theorem energy_trial_product_summable (u a : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ k, |a k| ≤ K) :
    Summable (fun k : ℕ => u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  have ht : Summable (fun k : ℕ => |u (k + 1)|) := (summable_nat_add_iff 1).mpr hu
  apply (ht.mul_left K).of_norm_bounded
  intro k
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| * K / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (ha _) (abs_nonneg _)) hkp.le
    _ ≤ |u (k + 1)| * K := div_le_self (mul_nonneg (abs_nonneg _) hK) hk
    _ = K * |u (k + 1)| := mul_comm _ _

end

section

open Polynomial Set
open scoped BigOperators

theorem realEnergy_damped_node_mem {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    realEnergyRho e x * x ∈ Ioo (-1 : ℝ) 1 := by
  have hr := realEnergyRho_mem he hx
  exact energy_mul_mem_Ioo ⟨by linarith [hr.1], hr.2⟩ hx

theorem energy_hasSum_power_square {N : ℕ} (e : ℝ) (x : Fin (n N) → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => realEnergyPowerMoment N e x k ^ 2 / (k : ℝ))
      (-(∑ i : Fin (n N), ∑ j : Fin (n N),
        Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
          (n N : ℝ) ^ 2) := by
  have hp (i j : Fin (n N)) := energy_hasSum_mul_power_div
    (realEnergy_damped_node_mem he (hx i)) (realEnergy_damped_node_mem he (hx j))
  have hs : HasSum
      (fun k : ℕ => ∑ i : Fin (n N), ∑ j : Fin (n N),
        ((realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j)) ^ k / (k : ℝ))
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        -Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => hp i j))
  have hc (k : ℕ) :
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        ((realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j)) ^ k / (k : ℝ)) =
      (∑ i : Fin (n N), realEnergyRho e (x i) ^ k * x i ^ k) ^ 2 / (k : ℝ) := by
    simp only [mul_pow]
    simpa only [one_mul, pow_two] using energy_sum_sum_mul_div
      (fun i : Fin (n N) => realEnergyRho e (x i) ^ k * x i ^ k)
      (fun i : Fin (n N) => realEnergyRho e (x i) ^ k * x i ^ k) 1 (k : ℝ)
  convert hs.mul_left (1 / (n N : ℝ) ^ 2) using 1
  · rfl
  · ext k
    rw [hc]
    unfold realEnergyPowerMoment
    simp only [div_eq_mul_inv]
    ring
  · simp only [Finset.sum_neg_distrib]
    ring

theorem energy_hasSum_column_square {N : ℕ} (hN : 0 < N)
    (e : ℝ) (s : Fin (n N) → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => 2 * realEnergyColumnMoment N e s k ^ 2 / (k : ℝ))
      (-(∑ i : Fin (n N), ∑ j : Fin (n N),
        realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
          (n N : ℝ) ^ 2 - Real.log 2) := by
  have hn0 : (n N : ℝ) ≠ 0 := by exact_mod_cast (show n N ≠ 0 by unfold n; omega)
  have hs' (i : Fin (n N)) : s i ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(hs i).1], (hs i).2.le⟩
  have hr (i j : Fin (n N)) :
      realEnergySigma e (s i) * realEnergySigma e (s j) ∈ Ico (0 : ℝ) 1 :=
    ⟨(mul_pos (realEnergySigma_mem he (hs i)).1 (realEnergySigma_mem he (hs j)).1).le,
      (realEnergySigma_mul_bounds he (hs i) (hs j)).2⟩
  have hp (i j : Fin (n N)) := energy_hasSum_cosine_kernel (hr i j) (hs' i) (hs' j)
  have hh : HasSum
      (fun k : ℕ => ∑ i : Fin (n N), ∑ j : Fin (n N),
        2 * (realEnergySigma e (s i) * realEnergySigma e (s j)) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s i) * (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ))
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        (-realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j) -
          Real.log 2)) := hasSum_sum (fun i _ => hasSum_sum (fun j _ => hp i j))
  have hc (k : ℕ) :
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        2 * (realEnergySigma e (s i) * realEnergySigma e (s j)) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s i) * (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ)) =
      2 * (∑ i : Fin (n N), realEnergySigma e (s i) ^ k *
        (Chebyshev.T ℝ (k : ℤ)).eval (s i)) ^ 2 / (k : ℝ) := by
    calc
      _ = ∑ i : Fin (n N), ∑ j : Fin (n N),
          2 * (realEnergySigma e (s i) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s i)) *
            (realEnergySigma e (s j) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s j)) / (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow]
        ring
      _ = _ := by rw [energy_sum_sum_mul_div]; ring
  convert hh.mul_left (1 / (n N : ℝ) ^ 2) using 1
  · rfl
  · ext k
    rw [hc]
    unfold realEnergyColumnMoment
    simp only [div_eq_mul_inv]
    ring
  · simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul]
    field_simp [hn0]

theorem energy_hasSum_mixed_moments {N : ℕ} (e : ℝ) (x s : Fin (n N) → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => 2 * realEnergyPowerMoment N e x k *
      realEnergyColumnMoment N e s k / (k : ℝ))
      (-(∑ i : Fin (n N), ∑ j : Fin (n N),
        Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
          (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / (n N : ℝ) ^ 2) := by
  have hs' (j : Fin (n N)) : s j ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(hs j).1], (hs j).2.le⟩
  have hz (i j : Fin (n N)) :
      realEnergyRho e (x i) * realEnergySigma e (s j) * x i ∈ Ioo (-1 : ℝ) 1 := by
    have hr := realEnergyRho_mem he (hx i)
    have ht := realEnergySigma_mem he (hs j)
    exact energy_mul_mem_Ioo
      (energy_mul_mem_Ioo ⟨by linarith [hr.1], hr.2⟩ ⟨by linarith [ht.1], ht.2⟩) (hx i)
  have hp (i j : Fin (n N)) := energy_hasSum_cross_kernel (hz i j) (hs' j)
  have hh : HasSum
      (fun k : ℕ => ∑ i : Fin (n N), ∑ j : Fin (n N),
        2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ))
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        -Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
          (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => hp i j))
  have hc (k : ℕ) :
      (∑ i : Fin (n N), ∑ j : Fin (n N),
        2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ)) =
      2 * (∑ i : Fin (n N), realEnergyRho e (x i) ^ k * x i ^ k) *
        (∑ j : Fin (n N), realEnergySigma e (s j) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s j)) / (k : ℝ) := by
    calc
      _ = ∑ i : Fin (n N), ∑ j : Fin (n N),
          2 * (realEnergyRho e (x i) ^ k * x i ^ k) *
            (realEnergySigma e (s j) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s j)) / (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [mul_pow]
        ring
      _ = _ := energy_sum_sum_mul_div _ _ _ _
  convert hh.mul_left (1 / (n N : ℝ) ^ 2) using 1
  · rfl
  · ext k
    rw [hc]
    unfold realEnergyPowerMoment realEnergyColumnMoment
    simp only [div_eq_mul_inv]
    ring
  · simp only [Finset.sum_neg_distrib]
    ring

theorem energy_hasSum_second_square {N : ℕ} (hN : 0 < N)
    (e : ℝ) (x s : Fin (n N) → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ =>
      (realEnergyPowerMoment N e x k - 2 * realEnergyColumnMoment N e s k) ^ 2 / (2 * (k : ℝ)))
      (-((∑ i : Fin (n N), ∑ j : Fin (n N),
          Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
            (2 * (n N : ℝ) ^ 2) +
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
            (n N : ℝ) ^ 2 -
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
            (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / (n N : ℝ) ^ 2 +
        Real.log 2)) := by
  have hp := (energy_hasSum_power_square e x he hx).mul_left (1 / 2 : ℝ)
  have hc := energy_hasSum_column_square hN e s he hs
  have hm := energy_hasSum_mixed_moments e x s he hx hs
  convert (hp.add hc).sub hm using 1
  · rfl
  · ext k
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem energy_hasSum_trialTau_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {x : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u (k + 1) * realEnergyCosineMoment N e x (k + 1) /
        ((k + 1 : ℕ) : ℝ))
      ((∑ i : Fin (n N), realEnergyTrialTau u e (x i)) / (n N : ℝ)) := by
  have hs : HasSum
      (fun k : ℕ => ∑ i : Fin (n N),
        u (k + 1) * realEnergyTau e ^ (k + 1) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (x i) / ((k + 1 : ℕ) : ℝ))
      (∑ i : Fin (n N), realEnergyTrialTau u e (x i)) := by
    apply hasSum_sum
    intro i hi
    exact (realEnergyTrialTau_summable u hu he (hx i)).hasSum
  convert hs.div_const (n N : ℝ) using 1
  rfl
  funext k
  simp only [realEnergyCosineMoment, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem energy_hasSum_trialRho_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {x : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u (k + 1) * realEnergyPowerMoment N e x (k + 1) /
        ((k + 1 : ℕ) : ℝ))
      ((∑ i : Fin (n N), realEnergyTrialRho u e (x i)) / (n N : ℝ)) := by
  have hs : HasSum
      (fun k : ℕ => ∑ i : Fin (n N),
        u (k + 1) * realEnergyRho e (x i) ^ (k + 1) * x i ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))
      (∑ i : Fin (n N), realEnergyTrialRho u e (x i)) := by
    apply hasSum_sum
    intro i hi
    exact (realEnergyTrialRho_summable u hu he (hx i)).hasSum
  convert hs.div_const (n N : ℝ) using 1
  rfl
  funext k
  simp only [realEnergyPowerMoment, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem energy_hasSum_trialSigma_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {s : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => u (k + 1) * realEnergyColumnMoment N e s (k + 1) /
        ((k + 1 : ℕ) : ℝ))
      ((∑ j : Fin (n N), realEnergyTrialSigma u e (s j)) / (n N : ℝ)) := by
  have hh : HasSum
      (fun k : ℕ => ∑ j : Fin (n N),
        u (k + 1) * realEnergySigma e (s j) ^ (k + 1) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (s j) / ((k + 1 : ℕ) : ℝ))
      (∑ j : Fin (n N), realEnergyTrialSigma u e (s j)) := by
    apply hasSum_sum
    intro j hj
    exact (realEnergyTrialSigma_summable u hu he (hs j)).hasSum
  convert hh.div_const (n N : ℝ) using 1
  rfl
  funext k
  simp only [realEnergyColumnMoment, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem energy_tsum_trialTau_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {x : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    (∑' k : ℕ, u (k + 1) * realEnergyCosineMoment N e x (k + 1) /
      ((k + 1 : ℕ) : ℝ)) =
      (∑ i : Fin (n N), realEnergyTrialTau u e (x i)) / (n N : ℝ) :=
  (energy_hasSum_trialTau_average u hu he hx).tsum_eq

theorem energy_tsum_trialRho_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {x : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    (∑' k : ℕ, u (k + 1) * realEnergyPowerMoment N e x (k + 1) /
      ((k + 1 : ℕ) : ℝ)) =
      (∑ i : Fin (n N), realEnergyTrialRho u e (x i)) / (n N : ℝ) :=
  (energy_hasSum_trialRho_average u hu he hx).tsum_eq

theorem energy_tsum_trialSigma_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {N : ℕ} {e : ℝ}
    {s : Fin (n N) → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    (∑' k : ℕ, u (k + 1) * realEnergyColumnMoment N e s (k + 1) /
      ((k + 1 : ℕ) : ℝ)) =
      (∑ j : Fin (n N), realEnergyTrialSigma u e (s j)) / (n N : ℝ) :=
  (energy_hasSum_trialSigma_average u hu he hs).tsum_eq

end

open Set
open scoped BigOperators

theorem energy_tangent_of_hasSum (u a : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {K S : ℝ} (hK : 0 ≤ K)
    (ha : ∀ k, |a k| ≤ K)
    (hS : HasSum (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) S) :
    -S ≤ barrierTrialNormSq u -
      2 * (∑' k : ℕ, u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  have huS : HasSum (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (barrierTrialNormSq u) := (energy_trial_norm_summable u hu).hasSum
  have hp := (energy_trial_product_summable u a hu hK ha).hasSum
  apply hasSum_le _ hS.neg (huS.sub (hp.mul_left 2))
  intro k
  have hbase : -a (k + 1) ^ 2 ≤ u (k + 1) ^ 2 - 2 * (u (k + 1) * a (k + 1)) := by
    nlinarith [sq_nonneg (a (k + 1) - u (k + 1))]
  convert div_le_div_of_nonneg_right hbase (Nat.cast_nonneg (k + 1)) using 1 <;> ring

theorem realEnergy_first_tangent {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    ((∑ i : Fin (n N), ∑ j : Fin (n N),
        realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) /
      (n N : ℝ) ^ 2 + Real.log 2) / 2 ≤
    barrierTrialNormSq u -
      2 * (∑' k : ℕ, u (k + 1) * realEnergyCosineMoment N e x (k + 1) /
        ((k + 1 : ℕ) : ℝ)) := by
  have hS : HasSum
      (fun k : ℕ => realEnergyCosineMoment N e x (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin (n N), ∑ j : Fin (n N),
          realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) /
        (n N : ℝ) ^ 2 + Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => realEnergyCosineMoment N e x k ^ 2 / (k : ℝ)) 1).2
    simpa using energy_hasSum_first_square hN he hx
  have ht := energy_tangent_of_hasSum u (realEnergyCosineMoment N e x) hu
    (by norm_num : (0 : ℝ) ≤ 1) (energy_cosineMoment_abs_le_one hN he hx) hS
  linarith

theorem realEnergy_second_tangent {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    (∑ i : Fin (n N), ∑ j : Fin (n N),
      Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
        (2 * (n N : ℝ) ^ 2) +
    (∑ i : Fin (n N), ∑ j : Fin (n N),
      realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
        (n N : ℝ) ^ 2 -
    (∑ i : Fin (n N), ∑ j : Fin (n N),
      Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
        (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / (n N : ℝ) ^ 2 +
      Real.log 2 ≤
    barrierTrialNormSq u / 2 -
      (∑' k : ℕ, u (k + 1) * realEnergyPowerMoment N e x (k + 1) / ((k + 1 : ℕ) : ℝ)) +
      2 * (∑' k : ℕ, u (k + 1) * realEnergyColumnMoment N e s (k + 1) /
        ((k + 1 : ℕ) : ℝ)) := by
  let a : ℕ → ℝ := fun k => realEnergyPowerMoment N e x k - 2 * realEnergyColumnMoment N e s k
  have hB := energy_trial_product_summable u (realEnergyPowerMoment N e x) hu
    (by norm_num : (0 : ℝ) ≤ 1) (energy_powerMoment_abs_le_one hN he hx)
  have hC := energy_trial_product_summable u (realEnergyColumnMoment N e s) hu
    (by norm_num : (0 : ℝ) ≤ 1) (energy_columnMoment_abs_le_one hN he hs)
  have hsplit :
      (∑' k : ℕ, u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ)) =
      (∑' k : ℕ, u (k + 1) * realEnergyPowerMoment N e x (k + 1) / ((k + 1 : ℕ) : ℝ)) -
      2 * (∑' k : ℕ, u (k + 1) * realEnergyColumnMoment N e s (k + 1) /
        ((k + 1 : ℕ) : ℝ)) := by
    apply HasSum.tsum_eq
    convert hB.hasSum.sub (hC.hasSum.mul_left 2) using 1
    rfl
    funext k
    dsimp [a]
    ring
  have hhalf := energy_hasSum_second_square hN e x s he hx hs
  have hfull := hhalf.mul_left 2
  have hS : HasSum (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (2 * (-((∑ i : Fin (n N), ∑ j : Fin (n N),
          Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
            (2 * (n N : ℝ) ^ 2) +
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
            (n N : ℝ) ^ 2 -
        (∑ i : Fin (n N), ∑ j : Fin (n N),
          Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
            (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / (n N : ℝ) ^ 2 +
        Real.log 2))) := by
    apply (hasSum_nat_add_iff (f := fun k : ℕ => a k ^ 2 / (k : ℝ)) 1).2
    simp only [Finset.sum_range_one, Nat.cast_zero, div_zero, add_zero]
    convert hfull using 1
    rfl
    funext k
    dsimp [a]
    ring
  have ht := energy_tangent_of_hasSum u a hu (by norm_num : (0 : ℝ) ≤ 3)
    (energy_secondMoment_abs_le_three hN he hx hs) hS
  rw [hsplit] at ht
  linarith

def realEnergyDampedInteraction (N : ℕ) (k e : ℝ) (x s : Fin (n N) → ℝ) : ℝ :=
  (k / 2) *
    (∑ i : Fin (n N), ∑ j : Fin (n N),
      realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / (n N : ℝ) ^ 2 +
  (∑ i : Fin (n N), ∑ j : Fin (n N),
    Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
      (2 * (n N : ℝ) ^ 2) +
  (∑ i : Fin (n N), ∑ j : Fin (n N),
    realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
      (n N : ℝ) ^ 2 -
  (∑ i : Fin (n N), ∑ j : Fin (n N),
    Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
      (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / (n N : ℝ) ^ 2


theorem realEnergyDampedInteraction_le_trials {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    realEnergyDampedInteraction N k e x s ≤ -(k / 2 + 1) * Real.log 2 +
      k * barrierTrialNormSq p + barrierTrialNormSq v / 2 -
      2 * k * (∑' j : ℕ, p (j + 1) * realEnergyCosineMoment N e x (j + 1) /
        ((j + 1 : ℕ) : ℝ)) -
      (∑' j : ℕ, v (j + 1) * realEnergyPowerMoment N e x (j + 1) / ((j + 1 : ℕ) : ℝ)) +
      2 * (∑' j : ℕ, v (j + 1) * realEnergyColumnMoment N e s (j + 1) /
        ((j + 1 : ℕ) : ℝ)) := by
  have hfirst := mul_le_mul_of_nonneg_left (realEnergy_first_tangent hN he hx p hp) hk
  have hsecond := realEnergy_second_tangent hN he hx hs v hv
  unfold realEnergyDampedInteraction
  simp only [div_eq_mul_inv, mul_inv_rev] at hfirst hsecond ⊢
  nlinarith only [hfirst, hsecond]

open Set
open scoped BigOperators

theorem energy_average_le_of_le_add {m : ℕ} (hm : 0 < m)
    (f g : Fin m → ℝ) (c : ℝ) (hfg : ∀ i, f i ≤ g i + c) :
    (∑ i, f i) / (m : ℝ) ≤ (∑ i, g i) / (m : ℝ) + c := by
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hfg i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hh
  calc
    _ ≤ ((∑ i, g i) + (m : ℝ) * c) / (m : ℝ) :=
      div_le_div_of_nonneg_right hh hmp.le
    _ = _ := by field_simp [hmp.ne']

theorem realEnergyDampedInteraction_le_trialAverages {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    realEnergyDampedInteraction N k e x s ≤ -(k / 2 + 1) * Real.log 2 +
      k * barrierTrialNormSq p + barrierTrialNormSq v / 2 +
      (∑ i : Fin (n N), (-2 * k * realEnergyTrialTau p e (x i) - realEnergyTrialRho v e (x i))) /
        (n N : ℝ) +
      (∑ j : Fin (n N), 2 * realEnergyTrialSigma v e (s j)) / (n N : ℝ) := by
  have hh := realEnergyDampedInteraction_le_trials hN hk he hx hs p v hp hv
  rw [energy_tsum_trialTau_average p hp he hx,
    energy_tsum_trialRho_average v hv he hx, energy_tsum_trialSigma_average v hv he hs] at hh
  apply hh.trans_eq
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem realEnergyDampedInteraction_le_canonicalTrials {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    realEnergyDampedInteraction N k e x s ≤ -(k / 2 + 1) * Real.log 2 +
      k * barrierTrialNormSq p + barrierTrialNormSq v / 2 +
      (∑ i : Fin (n N), (-2 * k * barrierTrialT p (x i) - barrierTrialS v (x i))) / (n N : ℝ) +
      (∑ j : Fin (n N), 2 * barrierTrialT v (s j)) / (n N : ℝ) +
      2 * k * e * (∑' j : ℕ, |p j|) + 4 * e * (∑' j : ℕ, |v j|) := by
  have hn : 0 < n N := by unfold n; omega
  have hxavg := energy_average_le_of_le_add hn
    (fun i => -2 * k * realEnergyTrialTau p e (x i) - realEnergyTrialRho v e (x i))
    (fun i => -2 * k * barrierTrialT p (x i) - barrierTrialS v (x i))
    (2 * k * e * (∑' j : ℕ, |p j|) + 2 * e * (∑' j : ℕ, |v j|)) (fun i => by
      have ht := (abs_le.mp (realEnergyTrialTau_sub_le p hp he (hx i))).1
      have hr := (abs_le.mp (realEnergyTrialRho_sub_le v hv he (hx i))).1
      have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * k by positivity)
      nlinarith only [hm, hr])
  have hsavg := energy_average_le_of_le_add hn
    (fun j => 2 * realEnergyTrialSigma v e (s j))
    (fun j => 2 * barrierTrialT v (s j))
    (2 * e * (∑' j : ℕ, |v j|)) (fun j => by
      have ht := (abs_le.mp (realEnergyTrialSigma_sub_le v hv he (hs j))).2
      linarith)
  have hd := realEnergyDampedInteraction_le_trialAverages hN hk he hx hs p v hp hv
  linarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealEnergyDiagonalSums
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Set
open scoped ComplexConjugate

theorem energy_log_chord_lower (z : ℂ) (hz : ‖z‖ = 1) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    Real.log (1 - r) ≤ Real.log ‖(1 : ℂ) - (r : ℂ) * z‖ := by
  have hn : ‖(r : ℂ) * z‖ = r := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1, hz, mul_one]
  have ht := norm_add_le ((1 : ℂ) - (r : ℂ) * z) ((r : ℂ) * z)
  rw [sub_add_cancel, norm_one, hn] at ht
  exact Real.log_le_log (sub_pos.mpr hr.2) (by linarith)

theorem realEnergyCosineKernel_lower {r u v : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    -Real.log 2 + 2 * Real.log (1 - r) ≤ realEnergyCosineKernel r u v := by
  have hn1 : ‖realEnergyCirclePoint u * realEnergyCirclePoint v‖ = 1 := by
    rw [Complex.norm_mul, realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have hn2 : ‖realEnergyCirclePoint u * conj (realEnergyCirclePoint v)‖ = 1 := by
    rw [Complex.norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have h1 := energy_log_chord_lower _ hn1 hr
  have h2 := energy_log_chord_lower _ hn2 hr
  unfold realEnergyCosineKernel
  linarith

theorem realEnergy_cosine_tau_diagonal_lower {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Icc (-1 : ℝ) 1) :
    -Real.log 2 + 2 * Real.log (1 - realEnergyTau e ^ 2) ≤
      realEnergyCosineKernel (realEnergyTau e ^ 2) x x := by
  have ht := realEnergyTau_bounds he
  have ht2 : realEnergyTau e ^ 2 < 1 := by
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  exact realEnergyCosineKernel_lower ⟨sq_pos_of_pos ht.1, ht2⟩ hx hx

theorem realEnergy_cosine_sigma_diagonal_lower {e s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    -Real.log 2 + 2 * Real.log e + Real.log (1 - s) ≤
      realEnergyCosineKernel (realEnergySigma e s ^ 2) s s := by
  have ht := realEnergySigma_mem he hs
  have ht2 : realEnergySigma e s ^ 2 < 1 := by
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2.le⟩
  have hk := realEnergyCosineKernel_lower ⟨sq_pos_of_pos ht.1, ht2⟩ hs' hs'
  have hd := realEnergy_log_sigma_diagonal_ge he hs
  linarith

end

open Set
open scoped BigOperators

theorem realEnergy_tau_diagonal_sum {N : ℕ} (hN : 0 < N)
    {e k : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hk : 0 ≤ k)
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    -(k / (2 * (n N : ℝ) ^ 2)) *
        (∑ i : Fin (n N), realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x i)) ≤
      k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * (n N : ℝ)) := by
  have hn : (0 : ℝ) < n N := by
    have hnpos : 0 < n N := by unfold n; omega
    exact Nat.cast_pos.mpr hnpos
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    realEnergy_cosine_tau_diagonal_lower he ⟨(hx i).1.le, (hx i).2.le⟩)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ k / (2 * (n N : ℝ) ^ 2) by positivity)
  have hc : k / (2 * (n N : ℝ) ^ 2) *
      ((n N : ℝ) * (-Real.log 2 + 2 * Real.log (1 - realEnergyTau e ^ 2))) =
      -(k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * (n N : ℝ))) := by
    field_simp [hn.ne']
    ring
  rw [hc] at hm
  linarith

theorem realEnergy_power_diagonal_sum {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    -(∑ i : Fin (n N), Real.log (1 - realEnergyRho e (x i) ^ 2 * x i ^ 2)) /
        (2 * (n N : ℝ) ^ 2) ≤
      -(∑ i : Fin (n N), Real.log (1 - x i)) / (2 * (n N : ℝ) ^ 2) +
        (Real.log 2 - Real.log e) / (2 * (n N : ℝ)) := by
  have hn : (0 : ℝ) < n N := by
    have hnpos : 0 < n N := by unfold n; omega
    exact Nat.cast_pos.mpr hnpos
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    realEnergy_log_power_diagonal_ge he (hx i))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hm := div_le_div_of_nonneg_right (neg_le_neg hb)
    (show 0 ≤ 2 * (n N : ℝ) ^ 2 by positivity)
  apply hm.trans_eq
  field_simp [hn.ne']
  ring

theorem realEnergy_sigma_diagonal_sum {N : ℕ} (hN : 0 < N)
    {e : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {s : Fin (n N) → ℝ} (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    -(∑ j : Fin (n N), realEnergyCosineKernel (realEnergySigma e (s j) ^ 2) (s j) (s j)) /
        (n N : ℝ) ^ 2 ≤
      -(∑ j : Fin (n N), Real.log (1 - s j)) / (n N : ℝ) ^ 2 +
        (Real.log 2 - 2 * Real.log e) / (n N : ℝ) := by
  have hn : (0 : ℝ) < n N := by
    have hnpos : 0 < n N := by unfold n; omega
    exact Nat.cast_pos.mpr hnpos
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    realEnergy_cosine_sigma_diagonal_lower he (hs j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hb
  have hm := div_le_div_of_nonneg_right (neg_le_neg hb) (sq_nonneg (n N : ℝ))
  apply hm.trans_eq
  field_simp [hn.ne']
  ring

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealEnergySupDual
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Set

theorem energy_damping_log_cost {e r : ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hrlo : (1 - e) ^ 2 ≤ r) (hrhi : r ≤ 1) : -Real.log r ≤ 4 * e := by
  have hrhalf : (1 / 2 : ℝ) ≤ r := by nlinarith [sq_nonneg e, he.1, he.2]
  have hr0 : 0 < r := by linarith
  have hgap : 1 - r ≤ 2 * e := by nlinarith [sq_nonneg e]
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at hl
  have hi : r⁻¹ - 1 = (1 - r) / r := by field_simp [hr0.ne']
  rw [hi] at hl
  apply hl.trans
  apply (div_le_iff₀ hr0).mpr
  have hp := mul_le_mul_of_nonneg_left hrhalf (show 0 ≤ 4 * e by linarith [he.1])
  nlinarith

theorem realEnergy_cosine_tau_le {e u v : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) (huv : u ≠ v) :
    Real.log |u - v| ≤ realEnergyCosineKernel (realEnergyTau e ^ 2) u v + 4 * e := by
  have ht := realEnergyTau_bounds he
  have htlo : (1 - e) ^ 2 ≤ realEnergyTau e ^ 2 := le_rfl
  have hthi : realEnergyTau e ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  have hc := realEnergyCosineKernel_compare hu hv huv (sq_pos_of_pos ht.1)
  have hec := energy_damping_log_cost he htlo hthi
  linarith

theorem realEnergy_cosine_sigma_le {e s t : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) (hst : s ≠ t) :
    Real.log |s - t| ≤
      realEnergyCosineKernel (realEnergySigma e s * realEnergySigma e t) s t + 4 * e := by
  have hr := realEnergySigma_mul_bounds he hs ht
  have hr0 := mul_pos (realEnergySigma_mem he hs).1 (realEnergySigma_mem he ht).1
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2.le⟩
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.le⟩
  have hc := realEnergyCosineKernel_compare hs' ht' hst hr0
  have hec := energy_damping_log_cost he hr.1 hr.2.le
  linarith

end

section

open Polynomial
open scoped BigOperators

private theorem trial_scalar_norm_le (a b : ℝ) {m : ℕ}
    (hm : 0 < m) (hb : |b| ≤ 1) : ‖a * b / (m : ℝ)‖ ≤ |a| := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_pos hm0]
  calc
    _ ≤ |a| * 1 / (m : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (abs_nonneg a)) hm0.le
    _ = |a| / (m : ℝ) := by rw [mul_one]
    _ ≤ |a| := div_le_self (abs_nonneg a) hm1

private theorem trial_abs_tail_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    (∑' k : ℕ, |u (k + 1)|) ≤ ∑' k : ℕ, |u k| := by
  have hsplit := hu.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  linarith [abs_nonneg (u 0)]

theorem barrierTrialT_abs_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {x : ℝ} (hx : |x| ≤ 1) :
    |barrierTrialT u x| ≤ ∑' k : ℕ, |u k| := by
  have hud : Summable (fun k : ℕ => |u (k + 1)|) :=
    (summable_nat_add_iff 1).mpr hu
  have hbound : ‖barrierTrialT u x‖ ≤ ∑' k : ℕ, |u (k + 1)| := by
    apply (barrierTrialT_summable u hu hx).hasSum.norm_le_of_bounded hud.hasSum
    intro k
    exact trial_scalar_norm_le (u (k + 1))
      ((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Nat.succ_pos k)
      (Chebyshev.abs_eval_T_real_le_one ((k + 1 : ℕ) : ℤ) hx)
  simpa only [Real.norm_eq_abs] using hbound.trans (trial_abs_tail_le u hu)

theorem barrierTrialS_abs_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {x : ℝ} (hx : |x| ≤ 1) :
    |barrierTrialS u x| ≤ ∑' k : ℕ, |u k| := by
  have hud : Summable (fun k : ℕ => |u (k + 1)|) :=
    (summable_nat_add_iff 1).mpr hu
  have hbound : ‖barrierTrialS u x‖ ≤ ∑' k : ℕ, |u (k + 1)| := by
    apply (barrierTrialS_summable u hu hx).hasSum.norm_le_of_bounded hud.hasSum
    intro k
    apply trial_scalar_norm_le (u (k + 1)) (x ^ (k + 1)) (Nat.succ_pos k)
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) hx
  simpa only [Real.norm_eq_abs] using hbound.trans (trial_abs_tail_le u hu)

end

section

open Polynomial Set
open scoped BigOperators

theorem energy_sum_pairs_of_symmetric (m : ℕ) (f : Fin m → Fin m → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) =
      2 * (∑ i, ∑ j ∈ Finset.Ioi i, f i j) + (∑ i, f i i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have htail := ih (fun i j => f i.succ j.succ)
      (fun i j => hf i.succ j.succ)
    have hfull : (∑ i, ∑ j, f i j) =
        f 0 0 + (∑ j : Fin m, f 0 j.succ) + (∑ i : Fin m, f i.succ 0) +
          (∑ i : Fin m, ∑ j : Fin m, f i.succ j.succ) := by
      simp only [Fin.sum_univ_succ, Finset.sum_add_distrib]
      ring
    have hpair : (∑ i, ∑ j ∈ Finset.Ioi i, f i j) =
        (∑ j : Fin m, f 0 j.succ) +
          (∑ i : Fin m, ∑ j ∈ Finset.Ioi i, f i.succ j.succ) := by
      rw [Fin.sum_univ_succ, Fin.sum_Ioi_zero]
      simp only [Fin.sum_Ioi_succ]
    have hdiag : (∑ i, f i i) = f 0 0 + (∑ i : Fin m, f i.succ i.succ) := by
      rw [Fin.sum_univ_succ]
    have hcross : (∑ i : Fin m, f i.succ 0) = ∑ i : Fin m, f 0 i.succ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hf i.succ 0
    rw [hfull, hpair, hdiag, hcross, htail]
    ring

theorem energy_sum_pairs_one (m : ℕ) :
    (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) = (m.choose 2 : ℝ) := by
  have hh := energy_sum_pairs_of_symmetric m (fun _ _ => (1 : ℝ))
    (fun _ _ => rfl)
  have hfull : (∑ _i : Fin m, ∑ _j : Fin m, (1 : ℝ)) = (m : ℝ) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    ring
  have hdiag : (∑ _i : Fin m, (1 : ℝ)) = (m : ℝ) := by simp
  rw [hfull, hdiag] at hh
  rw [Nat.cast_choose_two]
  nlinarith only [hh]

theorem energy_sum_pairs_const (m : ℕ) (c : ℝ) :
    (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, c) = c * (m.choose 2 : ℝ) := by
  calc
    _ = (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) * c := by
      simp only [Finset.sum_mul, one_mul]
    _ = _ := by rw [energy_sum_pairs_one]; ring

theorem energy_sum_pairs_le_of_le_add (m : ℕ)
    (f g : Fin m → Fin m → ℝ) (c : ℝ)
    (hfg : ∀ i j, i < j → f i j ≤ g i j + c) :
    (∑ i, ∑ j ∈ Finset.Ioi i, f i j) ≤
      (∑ i, ∑ j ∈ Finset.Ioi i, g i j) + c * (m.choose 2 : ℝ) := by
  calc
    _ ≤ ∑ i, ∑ j ∈ Finset.Ioi i, (g i j + c) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hfg i j (Finset.mem_Ioi.mp hj)
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [energy_sum_pairs_const]

theorem realEnergyCosineKernel_symm {r u v : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    realEnergyCosineKernel r u v = realEnergyCosineKernel r v u := by
  have hswap : HasSum (fun k : ℕ =>
      2 * r ^ k * (Chebyshev.T ℝ (k : ℤ)).eval v *
        (Chebyshev.T ℝ (k : ℤ)).eval u / (k : ℝ))
      (-realEnergyCosineKernel r u v - Real.log 2) := by
    convert energy_hasSum_cosine_kernel hr hu hv using 1
    funext k
    ring
  have heq := hswap.unique (energy_hasSum_cosine_kernel hr hv hu)
  linarith

end

section

open Set
open scoped BigOperators




def realEnergyFiniteValue (N : ℕ) (k : ℝ) (x s : Fin (n N) → ℝ) : ℝ :=
  ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 - (k + 1) / (2 * (n N : ℝ))) *
      Real.log 2 +
    (∑ i : Fin (n N), (realEnergyField k (x i) +
      (k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2))) / (n N : ℝ) +
    (∑ j : Fin (n N), realEnergyColumnField (s j)) / (n N : ℝ) +
    k * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / (n N : ℝ) ^ 2 +
    (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) / (n N : ℝ) ^ 2 +
    2 * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) / (n N : ℝ) ^ 2 -
    (∑ i : Fin (n N), ∑ j : Fin (n N), Real.log (1 - 2 * x i * s j + x i ^ 2)) /
      (n N : ℝ) ^ 2

theorem realEnergyMajorantOne_finite {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (realEnergyMajorantOne N x s) / (n N : ℝ) ^ 2 - Real.log 2 / 2 =
      realEnergyFiniteValue N 1 x s := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hC : 1 ≤ Cdegree N := Cdegree_pos hN
  rw [log_realEnergyMajorantOne hN x s hx hs hx0 hxi hsi]
  unfold realEnergyFiniteValue realEnergyField realEnergyColumnField
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Nat.cast_mul, Nat.cast_sub hC, Nat.cast_one]
  simp only [n, Cdegree, A, b, q, h, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hN0]
  ring

theorem realEnergyMajorantTwo_finite {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (realEnergyMajorantTwo N x s) / (n N : ℝ) ^ 2 - Real.log 2 / 2 =
      realEnergyFiniteValue N 2 x s := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hC : 1 ≤ Cdegree N := Cdegree_pos hN
  rw [log_realEnergyMajorantTwo hN x s hx hs hx0 hxi hsi]
  unfold realEnergyFiniteValue realEnergyField realEnergyColumnField
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Nat.cast_add, Nat.cast_mul, Nat.cast_sub hC, Nat.cast_one, Nat.cast_choose_two]
  simp only [n, Cdegree, A, b, q, h, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hN0]
  ring

end

section

open scoped BigOperators

theorem realEnergyCaseField_eq (x : ℝ) :
    realEnergyCaseField x = (1 - x ^ 2) / (1 + x ^ 2) - (5 / 6 : ℝ) := by
  unfold realEnergyCaseField
  have hd : 1 + x ^ 2 ≠ 0 := (realCoordinateInv_denominator_pos x).ne'
  field_simp [hd]
  ring

theorem realEnergyCaseField_average {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) :
    (∑ i : Fin (n N), realEnergyCaseField (x i)) / (n N : ℝ) =
      (∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) / (n N : ℝ) - 5 / 6 := by
  have hn0 : (n N : ℝ) ≠ 0 := by exact_mod_cast (show n N ≠ 0 by unfold n; omega)
  simp_rw [realEnergyCaseField_eq]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp [hn0]

theorem realEnergyCaseField_average_gt {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ)
    (hcase : ((n N - 1 - 2 * g N : ℕ) : ℝ) <
      ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) :
    -(1 / (n N : ℝ)) < (∑ i : Fin (n N), realEnergyCaseField (x i)) / (n N : ℝ) := by
  have hn : 1 ≤ n N := by unfold n; omega
  have hg : 2 * g N ≤ n N - 1 := by unfold n g; omega
  have hnpos : (0 : ℝ) < n N := by exact_mod_cast (show 0 < n N by omega)
  have hc : ((n N - 1 - 2 * g N : ℕ) : ℝ) = (5 / 6 : ℝ) * (n N : ℝ) - 1 := by
    rw [Nat.cast_sub hg, Nat.cast_sub hn, Nat.cast_one]
    simp only [n, g, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hd : ((n N - 1 - 2 * g N : ℕ) : ℝ) / (n N : ℝ) =
      5 / 6 - 1 / (n N : ℝ) := by
    rw [hc]
    field_simp [hnpos.ne']
  have he := div_lt_div_of_pos_right hcase hnpos
  rw [hd] at he
  rw [realEnergyCaseField_average hN x]
  linarith

theorem realEnergyCaseField_correction {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ)
    (hcase : ((n N - 1 - 2 * g N : ℕ) : ℝ) <
      ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2))
    (E lam : ℝ) (hlam : 0 ≤ lam) :
    E ≤ E + lam * ((∑ i : Fin (n N), realEnergyCaseField (x i)) / (n N : ℝ)) +
      lam / (n N : ℝ) := by
  have he := mul_le_mul_of_nonneg_left (realEnergyCaseField_average_gt hN x hcase).le hlam
  have hnorm : lam * (-(1 / (n N : ℝ))) = -(lam / (n N : ℝ)) := by ring
  rw [hnorm] at he
  linarith

end

open Set
open scoped BigOperators

def realEnergyOffDiagonalInteraction (N : ℕ) (k : ℝ) (x s : Fin (n N) → ℝ) : ℝ :=
  k * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / (n N : ℝ) ^ 2 +
  (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) / (n N : ℝ) ^ 2 +
  2 * (∑ i : Fin (n N), ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) / (n N : ℝ) ^ 2 -
  (∑ i : Fin (n N), ∑ j : Fin (n N), Real.log (1 - 2 * x i * s j + x i ^ 2)) /
    (n N : ℝ) ^ 2

theorem realEnergyOffDiagonalInteraction_le_damped {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    realEnergyOffDiagonalInteraction N k x s ≤
      realEnergyDampedInteraction N k e x s -
      k / (2 * (n N : ℝ) ^ 2) *
        (∑ i : Fin (n N), realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x i)) -
      (∑ i : Fin (n N), Real.log (1 - (realEnergyRho e (x i) * x i) ^ 2)) /
        (2 * (n N : ℝ) ^ 2) -
      (∑ j : Fin (n N), realEnergyCosineKernel (realEnergySigma e (s j) ^ 2) (s j) (s j)) /
        (n N : ℝ) ^ 2 +
      (4 * k + 12) * e * ((n N).choose 2 : ℝ) / (n N : ℝ) ^ 2 + 6 * e := by
  have hn : (0 : ℝ) < n N := by
    have hnpos : 0 < n N := by unfold n; omega
    exact Nat.cast_pos.mpr hnpos
  let F : Fin (n N) → Fin (n N) → ℝ := fun i j =>
    realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)
  let G : Fin (n N) → Fin (n N) → ℝ := fun i j =>
    Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))
  let H : Fin (n N) → Fin (n N) → ℝ := fun i j =>
    realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)
  let Q : Fin (n N) → Fin (n N) → ℝ := fun i j =>
    Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
      (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)
  have hF := energy_sum_pairs_le_of_le_add (n N)
    (fun i j => Real.log |x j - x i|) F (4 * e) (fun i j hij => by
      dsimp [F]
      rw [abs_sub_comm (x j) (x i)]
      exact realEnergy_cosine_tau_le he ⟨(hx i).1.le, (hx i).2.le⟩
        ⟨(hx j).1.le, (hx j).2.le⟩ (fun h => (ne_of_lt hij) (hxi h)))
  have hG := energy_sum_pairs_le_of_le_add (n N)
    (fun i j => Real.log (1 - x i * x j)) G (4 * e) (fun i j _ => by
      have hc := realEnergy_power_kernel_le he (hx i) (hx j)
      dsimp [G]
      convert hc using 1; congr 2; ring)
  have hH := energy_sum_pairs_le_of_le_add (n N)
    (fun i j => Real.log |s j - s i|) H (4 * e) (fun i j hij => by
      dsimp [H]
      rw [abs_sub_comm (s j) (s i)]
      exact realEnergy_cosine_sigma_le he (hs i) (hs j)
        (fun h => (ne_of_lt hij) (hsi h)))
  have hQ :
      -(∑ i : Fin (n N), ∑ j : Fin (n N), Real.log (1 - 2 * x i * s j + x i ^ 2)) ≤
      -(∑ i : Fin (n N), ∑ j : Fin (n N), Q i j) + 6 * e * (n N : ℝ) ^ 2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => realEnergy_cross_kernel_le he (hx i) (hs j)))
    simpa only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Q, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hh
  have ht := realEnergyTau_bounds he
  have htr : realEnergyTau e ^ 2 ∈ Ico (0 : ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hFsym (i j : Fin (n N)) : F i j = F j i :=
    realEnergyCosineKernel_symm htr ⟨(hx i).1.le, (hx i).2.le⟩ ⟨(hx j).1.le, (hx j).2.le⟩
  have hGsym (i j : Fin (n N)) : G i j = G j i := by dsimp [G]; rw [mul_comm]
  have hHsym (i j : Fin (n N)) : H i j = H j i := by
    have hi := realEnergySigma_mem he (hs i)
    have hj := realEnergySigma_mem he (hs j)
    have hr : realEnergySigma e (s i) * realEnergySigma e (s j) ∈ Ico (0 : ℝ) 1 :=
      ⟨mul_nonneg hi.1.le hj.1.le, (realEnergySigma_mul_bounds he (hs i) (hs j)).2⟩
    dsimp [H]
    rw [realEnergyCosineKernel_symm hr
      ⟨by linarith [(hs i).1], (hs i).2.le⟩ ⟨by linarith [(hs j).1], (hs j).2.le⟩]
    rw [mul_comm]
  have hpF : (∑ i, ∑ j ∈ Finset.Ioi i, F i j) =
      ((∑ i, ∑ j, F i j) - ∑ i, F i i) / 2 := by
    linarith [energy_sum_pairs_of_symmetric (n N) F hFsym]
  have hpG : (∑ i, ∑ j ∈ Finset.Ioi i, G i j) =
      ((∑ i, ∑ j, G i j) - ∑ i, G i i) / 2 := by
    linarith [energy_sum_pairs_of_symmetric (n N) G hGsym]
  have hpH : (∑ i, ∑ j ∈ Finset.Ioi i, H i j) =
      ((∑ i, ∑ j, H i j) - ∑ i, H i i) / 2 := by
    linarith [energy_sum_pairs_of_symmetric (n N) H hHsym]
  have hh := add_le_add
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hF hk) hG)
      (mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 2))) hQ
  have hd := div_le_div_of_nonneg_right hh (sq_nonneg (n N : ℝ))
  calc
    realEnergyOffDiagonalInteraction N k x s =
        (k * (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) +
          (∑ i, ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) +
          2 * (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) +
          -(∑ i, ∑ j, Real.log (1 - 2 * x i * s j + x i ^ 2))) / (n N : ℝ) ^ 2 := by
      unfold realEnergyOffDiagonalInteraction
      ring
    _ ≤ _ := hd
    _ = _ := by
      rw [hpF, hpG, hpH]
      dsimp [F, G, H, Q, realEnergyDampedInteraction]
      simp only [pow_two]
      field_simp [hn.ne']; ring

def realEnergyRegularizationError (N : ℕ) (k e : ℝ) : ℝ :=
  2 * Real.log 2 / (n N : ℝ) +
    k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * (n N : ℝ)) +
    (Real.log 2 - Real.log e) / (2 * (n N : ℝ)) +
    (Real.log 2 - 2 * Real.log e) / (n N : ℝ) +
    (4 * k + 12) * e * ((n N).choose 2 : ℝ) / (n N : ℝ) ^ 2 + 6 * e

theorem realEnergyFiniteValue_le_regularized {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : k = 1 ∨ k = 2) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {x s : Fin (n N) → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    realEnergyFiniteValue N k x s ≤
      ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 - (k + 1) / (2 * (n N : ℝ))) *
        Real.log 2 +
      (∑ i : Fin (n N), (realEnergyField k (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) +
      (∑ j : Fin (n N), (realEnergyColumnField (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) +
      realEnergyDampedInteraction N k e x s + realEnergyRegularizationError N k e := by
  have hn : (n N : ℝ) ≠ 0 := by
    have hnpos : 0 < n N := by unfold n; omega
    exact (Nat.cast_pos.mpr hnpos).ne'
  have hk0 : 0 ≤ k := by
    rcases hk with rfl | rfl <;> norm_num
  have hcorrection :
      (∑ i : Fin (n N), ((k + 2) / (2 * (n N : ℝ)) *
        Real.log (1 + x i ^ 2))) / (n N : ℝ) ≤ 2 * Real.log 2 / (n N : ℝ) := by
    convert (realEnergyFiniteCorrection_bounds hN k hk x hx).2 using 1; ring
  have hinteraction := realEnergyOffDiagonalInteraction_le_damped hN hk0 he hx hs hxi hsi
  have htau := realEnergy_tau_diagonal_sum hN he hk0 hx
  have hpower := realEnergy_power_diagonal_sum hN he hx
  have hsigma := realEnergy_sigma_diagonal_sum hN he hs

  simp only [mul_pow] at hinteraction
  simp only [neg_mul] at htau
  simp only [neg_div] at hpower hsigma
  have hsplit : realEnergyFiniteValue N k x s =
      ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 - (k + 1) / (2 * (n N : ℝ))) *
        Real.log 2 +
      (∑ i : Fin (n N), realEnergyField k (x i)) / (n N : ℝ) +
      (∑ j : Fin (n N), realEnergyColumnField (s j)) / (n N : ℝ) +
      (∑ i : Fin (n N), ((k + 2) / (2 * (n N : ℝ)) *
        Real.log (1 + x i ^ 2))) / (n N : ℝ) +
      realEnergyOffDiagonalInteraction N k x s := by
    unfold realEnergyFiniteValue realEnergyOffDiagonalInteraction
    rw [Finset.sum_add_distrib]
    ring
  have hrow :
      (∑ i : Fin (n N), (realEnergyField k (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) =
      (∑ i : Fin (n N), realEnergyField k (x i)) / (n N : ℝ) -
        (∑ i : Fin (n N), Real.log (1 - x i)) / (2 * (n N : ℝ) ^ 2) := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
    field_simp [hn]
  have hcolumn :
      (∑ j : Fin (n N), (realEnergyColumnField (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) =
      (∑ j : Fin (n N), realEnergyColumnField (s j)) / (n N : ℝ) -
        (∑ j : Fin (n N), Real.log (1 - s j)) / (n N : ℝ) ^ 2 := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
    field_simp [hn]
  rw [hsplit, hrow, hcolumn]
  unfold realEnergyRegularizationError
  linarith only [hcorrection, hinteraction, htau, hpower, hsigma]



theorem realEnergyFiniteValue_le_trialFields {N : ℕ} (hN : 0 < N)
    {k e lam : ℝ} (hk : k = 1 ∨ k = 2) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hlam : 0 ≤ lam) {x s : Fin (n N) → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hcase : lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) <
      ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)))
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    realEnergyFiniteValue N k x s ≤
      (-(11 / 16 : ℝ) - (k + 1) / (2 * (n N : ℝ))) * Real.log 2 +
      k * barrierTrialNormSq p + barrierTrialNormSq v / 2 +
      (∑ i : Fin (n N), (realEnergyRowTrialField k lam p v (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) +
      (∑ j : Fin (n N), (realEnergyColumnTrialField v (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) +
      realEnergyRegularizationError N k e +
      2 * k * e * (∑' j : ℕ, |p j|) + 4 * e * (∑' j : ℕ, |v j|) + lam / (n N : ℝ) := by
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  have hfinite := realEnergyFiniteValue_le_regularized hN hk he hx hs hxi hsi
  have hdual := realEnergyDampedInteraction_le_canonicalTrials hN hk0 he hx hs p v hp hv
  have hcaseAdd : 0 ≤ lam * ((∑ i : Fin (n N), realEnergyCaseField (x i)) / (n N : ℝ)) +
      lam / (n N : ℝ) := by
    rcases hcase with hlam0 | hfail
    · simp [hlam0]
    · simpa only [zero_add] using realEnergyCaseField_correction hN x hfail 0 lam hlam
  have hrow :
      (∑ i : Fin (n N), (realEnergyRowTrialField k lam p v (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) =
      (∑ i : Fin (n N), (realEnergyField k (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) +
      (∑ i : Fin (n N), (-2 * k * barrierTrialT p (x i) - barrierTrialS v (x i))) / (n N : ℝ) +
      lam * ((∑ i : Fin (n N), realEnergyCaseField (x i)) / (n N : ℝ)) := by
    unfold realEnergyRowTrialField
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hcolumn :
      (∑ j : Fin (n N), (realEnergyColumnTrialField v (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) =
      (∑ j : Fin (n N), (realEnergyColumnField (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) +
      (∑ j : Fin (n N), 2 * barrierTrialT v (s j)) / (n N : ℝ) := by
    unfold realEnergyColumnTrialField
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hconstant := congrArg (fun z : ℝ => z * Real.log 2) (energy_constant_after_squares hN k)
  norm_num only at hconstant
  rw [hrow, hcolumn]
  simp only [div_eq_mul_inv, mul_inv_rev] at hfinite hdual hcaseAdd hconstant ⊢
  nlinarith only [hfinite, hdual, hcaseAdd, hconstant]

theorem realEnergyRowTrialField_residual_le {k lam x : ℝ}
    (hk : 0 ≤ k) (hlam : 0 ≤ lam) (hx : |x| ≤ 1)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    realEnergyRowTrialField k lam p v x - (1 / 12 : ℝ) * Real.log (1 - x) ≤
      lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) := by
  have habs := Real.log_nonpos (abs_nonneg x) hx
  have hquad := Real.log_nonneg (show (1 : ℝ) ≤ 1 + x ^ 2 by nlinarith [sq_nonneg x])
  have hD : realEnergyCaseField x ≤ (1 / 6 : ℝ) := by
    unfold realEnergyCaseField
    have hh : 0 ≤ 2 * x ^ 2 / (1 + x ^ 2) := by positivity
    linarith
  have hlamD := mul_le_mul_of_nonneg_left hD hlam
  have hT := mul_le_mul_of_nonneg_left (abs_le.mp (barrierTrialT_abs_le p hp hx)).1
    (show 0 ≤ 2 * k by positivity)
  have hS := (abs_le.mp (barrierTrialS_abs_le v hv hx)).1
  have hlog := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 19 / 48) habs
  have hlogq := mul_nonneg (show 0 ≤ k / 2 + 17 / 48 by positivity) hquad
  unfold realEnergyRowTrialField realEnergyField
  nlinarith only [hlamD, hT, hS, hlog, hlogq]

theorem realEnergyColumnTrialField_residual_le {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (v : ℕ → ℝ) (hv : Summable (fun j => |v j|)) :
    realEnergyColumnTrialField v s - (1 / 12 : ℝ) * Real.log (1 - s) ≤
      2 * (∑' j : ℕ, |v j|) := by
  have hlog := Real.log_nonpos hs.1.le hs.2.le
  have hsabs : |s| ≤ 1 := by rw [abs_of_pos hs.1]; exact hs.2.le
  have hT := (abs_le.mp (barrierTrialT_abs_le v hv hsabs)).2
  unfold realEnergyColumnTrialField realEnergyColumnField
  linarith

theorem energy_endpoint_convex_bound {G L B H d : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hG : G ≤ B) (hH : G - L / 12 ≤ H) :
    G - d * L / 12 ≤ B + d * (H - B) := by
  have hfirst := mul_le_mul_of_nonneg_left hG (sub_nonneg.mpr hd1)
  have hsecond := mul_le_mul_of_nonneg_left hH hd0
  nlinarith only [hfirst, hsecond]

theorem realEnergyRowTrialField_weaken_le {N : ℕ} (hN : 0 < N)
    {k lam x B : ℝ} (hk : 0 ≤ k) (hlam : 0 ≤ lam) (hx : |x| ≤ 1)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hB : realEnergyRowTrialField k lam p v x ≤ B) :
    realEnergyRowTrialField k lam p v x - Real.log (1 - x) / (2 * (n N : ℝ)) ≤
      B + 6 * (lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) - B) / (n N : ℝ) := by
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hn6 : (6 : ℝ) ≤ n N := by
    exact_mod_cast (show 6 ≤ n N by unfold n; omega)
  have hd0 : (0 : ℝ) ≤ 6 / (n N : ℝ) := by positivity
  have hd1 : (6 : ℝ) / (n N : ℝ) ≤ 1 := (div_le_iff₀ hn).mpr (by simpa using hn6)
  have hr := realEnergyRowTrialField_residual_le hk hlam hx p v hp hv
  have hres : realEnergyRowTrialField k lam p v x - Real.log (1 - x) / 12 ≤
      lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) := by
    convert hr using 1; ring
  convert energy_endpoint_convex_bound hd0 hd1 hB hres using 1 <;> ring

theorem realEnergyColumnTrialField_weaken_le {N : ℕ} (hN : 0 < N)
    {s B : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (v : ℕ → ℝ) (hv : Summable (fun j => |v j|))
    (hB : realEnergyColumnTrialField v s ≤ B) :
    realEnergyColumnTrialField v s - Real.log (1 - s) / (n N : ℝ) ≤
      B + 12 * (2 * (∑' j : ℕ, |v j|) - B) / (n N : ℝ) := by
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hn12 : (12 : ℝ) ≤ n N := by
    exact_mod_cast (show 12 ≤ n N by unfold n; omega)
  have hd0 : (0 : ℝ) ≤ 12 / (n N : ℝ) := by positivity
  have hd1 : (12 : ℝ) / (n N : ℝ) ≤ 1 := (div_le_iff₀ hn).mpr (by simpa using hn12)
  have hr := realEnergyColumnTrialField_residual_le hs v hv
  have hres : realEnergyColumnTrialField v s - Real.log (1 - s) / 12 ≤
      2 * (∑' j : ℕ, |v j|) := by convert hr using 1; ring
  convert energy_endpoint_convex_bound hd0 hd1 hB hres using 1 <;> ring


def realEnergyDualDampingCoefficient (k : ℝ) (p v : ℕ → ℝ) : ℝ :=
  2 * k + 12 + 2 * k * (∑' j : ℕ, |p j|) + 4 * (∑' j : ℕ, |v j|)

def realEnergyDualFiniteCoefficient (k e lam : ℝ) (p v : ℕ → ℝ) (Bx Bs : ℝ) : ℝ :=
  2 * Real.log 2 + k / 2 * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) +
    (Real.log 2 - Real.log e) / 2 + (Real.log 2 - 2 * Real.log e) + lam +
    6 * (lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) - Bx) +
    12 * (2 * (∑' j : ℕ, |v j|) - Bs)

theorem realEnergyRegularizationError_le {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : 0 ≤ k) (he : 0 ≤ e) :
    realEnergyRegularizationError N k e ≤
      (2 * Real.log 2 + k / 2 * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) +
        (Real.log 2 - Real.log e) / 2 + (Real.log 2 - 2 * Real.log e)) / (n N : ℝ) +
      (2 * k + 12) * e := by
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hc : ((n N).choose 2 : ℝ) ≤ (n N : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith only [hn.le]
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (4 * k + 12) * e by positivity)
  have hh : (4 * k + 12) * e * ((n N).choose 2 : ℝ) / (n N : ℝ) ^ 2 ≤
      (2 * k + 6) * e := by
    apply (div_le_div_of_nonneg_right hm (sq_nonneg (n N : ℝ))).trans_eq
    field_simp [hn.ne']; ring
  unfold realEnergyRegularizationError
  simp only [div_eq_mul_inv, mul_inv_rev] at hh ⊢
  nlinarith only [hh]

theorem realEnergyFiniteValue_le_uniformDual {N : ℕ} (hN : 0 < N)
    {k e lam Bx Bs : ℝ} (hk : k = 1 ∨ k = 2) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hlam : 0 ≤ lam) {x s : Fin (n N) → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hcase : lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) <
      ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)))
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField k lam p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs) :
    realEnergyFiniteValue N k x s ≤ realEnergyDualConstant k p v Bx Bs +
      e * realEnergyDualDampingCoefficient k p v +
      realEnergyDualFiniteCoefficient k e lam p v Bx Bs / (n N : ℝ) := by
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  have hrow :
      (∑ i : Fin (n N), (realEnergyRowTrialField k lam p v (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) ≤
      Bx + 6 * (lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) - Bx) / (n N : ℝ) := by
    apply (div_le_iff₀ hn).mpr
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      realEnergyRowTrialField_weaken_le hN hk0 hlam
        (abs_le.mpr ⟨(hx i).1.le, (hx i).2.le⟩) p v hp hv
        (hBx (x i) ⟨(hx i).1.le, (hx i).2⟩ (hx0 i)))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hh
  have hcolumn :
      (∑ j : Fin (n N), (realEnergyColumnTrialField v (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) ≤
      Bs + 12 * (2 * (∑' j : ℕ, |v j|) - Bs) / (n N : ℝ) := by
    apply (div_le_iff₀ hn).mpr
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      realEnergyColumnTrialField_weaken_le hN (hs j) v hv (hBs (s j) (hs j)))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hh
  have hfinite := realEnergyFiniteValue_le_trialFields hN hk he hlam hx hs hxi hsi hcase p v hp hv
  have herror := realEnergyRegularizationError_le hN hk0 he.1.le
  have hconst : (-(11 / 16 : ℝ) - (k + 1) / (2 * (n N : ℝ))) * Real.log 2 ≤
      -(11 / 16 : ℝ) * Real.log 2 := by
    have hh : 0 ≤ ((k + 1) / (2 * (n N : ℝ))) * Real.log 2 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    nlinarith only [hh]
  unfold realEnergyDualConstant realEnergyDualDampingCoefficient realEnergyDualFiniteCoefficient
  simp only [div_eq_mul_inv, mul_inv_rev] at hrow hcolumn hfinite herror hconst ⊢
  nlinarith only [hrow, hcolumn, hfinite, herror, hconst]

theorem realEnergyDualDampingCoefficient_nonneg {k : ℝ} (hk : 0 ≤ k)
    (p v : ℕ → ℝ) : 0 ≤ realEnergyDualDampingCoefficient k p v := by
  have hp : 0 ≤ ∑' j : ℕ, |p j| := tsum_nonneg (fun _ => abs_nonneg _)
  have hv : 0 ≤ ∑' j : ℕ, |v j| := tsum_nonneg (fun _ => abs_nonneg _)
  unfold realEnergyDualDampingCoefficient
  positivity

theorem realEnergy_uniform_dual_eventually
    {k lam Bx Bs : ℝ} (hk : k = 1 ∨ k = 2) (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField k lam p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2))) →
      realEnergyFiniteValue N k x s ≤ realEnergyDualConstant k p v Bx Bs + d := by
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  let D : ℝ := realEnergyDualDampingCoefficient k p v
  have hD : 0 ≤ D := realEnergyDualDampingCoefficient_nonneg hk0 p v
  let e : ℝ := min (1 / 16) (d / (2 * (D + 1)))
  have he0 : 0 < e := by
    apply lt_min (by norm_num)
    exact div_pos hd (by positivity)
  have he8 : e < (1 / 8 : ℝ) := by
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have he : e ∈ Ioo (0 : ℝ) (1 / 8) := ⟨he0, he8⟩
  have heD : e * D < d / 2 := by
    have heSmall : e ≤ d / (2 * (D + 1)) := min_le_right _ _
    have hprod := (le_div_iff₀ (show 0 < 2 * (D + 1) by positivity)).mp heSmall
    nlinarith only [hprod, he0]
  let C : ℝ := realEnergyDualFiniteCoefficient k e lam p v Bx Bs
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * |C| / d)
  refine ⟨M + 1, ?_⟩
  intro N hNlarge x s hx hs hx0 hxi hsi hcase
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hMN : M ≤ n N := by unfold n; omega
  have hbig : 2 * |C| / d < (n N : ℝ) :=
    hM.trans_le (Nat.cast_le.mpr hMN)
  have hCabs : |C| / (n N : ℝ) < d / 2 := by
    apply (div_lt_iff₀ hn).mpr
    have hprod := (div_lt_iff₀ hd).mp hbig
    nlinarith only [hprod]
  have hC : C / (n N : ℝ) < d / 2 :=
    (div_le_div_of_nonneg_right (le_abs_self C) hn.le).trans_lt hCabs
  have hfinite := realEnergyFiniteValue_le_uniformDual hN hk he hlam hx hs hx0 hxi hsi
    hcase p v hp hv hBx hBs
  change realEnergyFiniteValue N k x s ≤ realEnergyDualConstant k p v Bx Bs +
    e * D + C / (n N : ℝ) at hfinite
  linarith only [hfinite, heD, hC]

theorem realEnergyMajorantOne_uniform_dual {lam Bx Bs : ℝ} (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 1 lam p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) →
      Real.log (realEnergyMajorantOne N x s) / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        realEnergyDualConstant 1 p v Bx Bs + d := by
  obtain ⟨M, hM⟩ := realEnergy_uniform_dual_eventually (Or.inl rfl) hlam p v hp hv hBx hBs hd
  refine ⟨M + 1, ?_⟩
  intro N hNlarge x s hx hs hx0 hxi hsi hcase
  have hN : 0 < N := by omega
  rw [realEnergyMajorantOne_finite hN x s hx hs hx0 hxi hsi]
  exact hM N (by omega) x s hx hs hx0 hxi hsi (Or.inr hcase)

theorem realEnergyMajorantTwo_uniform_dual {Bx Bs : ℝ}
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 2 0 p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      Real.log (realEnergyMajorantTwo N x s) / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        realEnergyDualConstant 2 p v Bx Bs + d := by
  obtain ⟨M, hM⟩ := realEnergy_uniform_dual_eventually (Or.inr rfl) (le_refl (0 : ℝ))
    p v hp hv hBx hBs hd
  refine ⟨M + 1, ?_⟩
  intro N hNlarge x s hx hs hx0 hxi hsi
  have hN : 0 < N := by omega
  rw [realEnergyMajorantTwo_finite hN x s hx hs hx0 hxi hsi]
  exact hM N (by omega) x s hx hs hx0 hxi hsi (Or.inl rfl)

open Set
open scoped BigOperators



theorem realEnergyRowTrialField_image_bddAbove {k lam : ℝ}
    (hk : 0 ≤ k) (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|)) :
    BddAbove (realEnergyRowTrialField k lam p v '' {x : ℝ | x ∈ Ico (-1 : ℝ) 1 ∧ x ≠ 0}) := by
  refine ⟨lam / 6 + 2 * k * (∑' j : ℕ, |p j|) + (∑' j : ℕ, |v j|) + Real.log 2 / 12, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have habs : |x| ≤ 1 := abs_le.mpr ⟨hx.1.1, hx.1.2.le⟩
  have hres := realEnergyRowTrialField_residual_le hk hlam habs p v hp hv
  have hlog : Real.log (1 - x) ≤ Real.log 2 :=
    Real.log_le_log (sub_pos.mpr hx.1.2) (by linarith [hx.1.1])
  linarith

theorem realEnergyColumnTrialField_image_bddAbove
    (v : ℕ → ℝ) (hv : Summable (fun j => |v j|)) :
    BddAbove (realEnergyColumnTrialField v '' Ioo (0 : ℝ) 1) := by
  refine ⟨2 * (∑' j : ℕ, |v j|), ?_⟩
  rintro y ⟨s, hs, rfl⟩
  have hres := realEnergyColumnTrialField_residual_le hs v hv
  have hlog : Real.log (1 - s) ≤ 0 :=
    Real.log_nonpos (sub_pos.mpr hs.2).le (by linarith [hs.1])
  linarith



theorem realEnergyRowTrialField_le_sup {k lam : ℝ}
    (hk : 0 ≤ k) (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    {x : ℝ} (hx : x ∈ Ico (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    realEnergyRowTrialField k lam p v x ≤ realEnergyRowTrialSup k lam p v := by
  exact le_csSup (realEnergyRowTrialField_image_bddAbove hk hlam p v hp hv) ⟨x, ⟨hx, hx0⟩, rfl⟩

theorem realEnergyColumnTrialField_le_sup
    (v : ℕ → ℝ) (hv : Summable (fun j => |v j|)) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    realEnergyColumnTrialField v s ≤ realEnergyColumnTrialSup v := by
  exact le_csSup (realEnergyColumnTrialField_image_bddAbove v hv) ⟨s, hs, rfl⟩


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealEnergyMajorantExponential
namespace OAI


noncomputable section
open Set
open scoped BigOperators

namespace InternalCatalan

theorem energy_le_exp_of_normalized_log_le {a m L : ℝ} (hm : 0 < m)
    (h : Real.log a / m ^ 2 - Real.log 2 / 2 ≤ L) :
    a ≤ Real.exp (m ^ 2 * (L + Real.log 2 / 2)) := by
  have hlog : Real.log a / m ^ 2 ≤ L + Real.log 2 / 2 := by linarith only [h]
  have hscaled : Real.log a ≤ m ^ 2 * (L + Real.log 2 / 2) := by
    simpa only [mul_comm] using (div_le_iff₀ (sq_pos_of_pos hm)).mp hlog
  exact (Real.le_exp_log a).trans (Real.exp_le_exp.mpr hscaled)

theorem realEnergyMajorantOne_uniform_exp {lam Bx Bs : ℝ} (hlam : 0 ≤ lam)
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 1 lam p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) →
      realEnergyMajorantOne N x s ≤
        Real.exp ((n N : ℝ) ^ 2 *
          (realEnergyDualConstant 1 p v Bx Bs + d + Real.log 2 / 2)) := by
  obtain ⟨M, hM⟩ := realEnergyMajorantOne_uniform_dual hlam p v hp hv hBx hBs hd
  refine ⟨M + 1, ?_⟩
  intro N hNlarge x s hx hs hx0 hxi hsi hcase
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  apply energy_le_exp_of_normalized_log_le hn
  exact hM N (by omega) x s hx hs hx0 hxi hsi hcase

theorem realEnergyMajorantTwo_uniform_exp {Bx Bs : ℝ}
    (p v : ℕ → ℝ) (hp : Summable (fun j => |p j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 2 0 p v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      realEnergyMajorantTwo N x s ≤
        Real.exp ((n N : ℝ) ^ 2 *
          (realEnergyDualConstant 2 p v Bx Bs + d + Real.log 2 / 2)) := by
  obtain ⟨M, hM⟩ := realEnergyMajorantTwo_uniform_dual p v hp hv hBx hBs hd
  refine ⟨M + 1, ?_⟩
  intro N hNlarge x s hx hs hx0 hxi hsi
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  apply energy_le_exp_of_normalized_log_le hn
  exact hM N (by omega) x s hx hs hx0 hxi hsi

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RealDeterminantUpper
namespace OAI


noncomputable section
open Filter
open scoped Topology

namespace InternalCatalan


def realDeterminantPrefactor (N : ℕ) : ℝ :=
  (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N / ((n N).factorial : ℝ) ^ 2

theorem realDeterminantSheetPrefactor_nonneg (N : ℕ) :
    0 ≤ realDeterminantSheetPrefactor N := by
  apply le_trans _ (le_max_left _ _)
  exact pow_nonneg (by positivity) _


theorem realDeterminant_factorial_sq_one_le (N : ℕ) :
    (1 : ℝ) ≤ ((n N).factorial : ℝ) ^ 2 := by
  have hf : (1 : ℝ) ≤ ((n N).factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (n N)))
  nlinarith [sq_nonneg (((n N).factorial : ℝ) - 1)]

theorem realDeterminantPrefactor_le_mass_mul_sheet (N : ℕ) :
    realDeterminantPrefactor N ≤ (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N := by
  exact div_le_self
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (realDeterminantSheetPrefactor_nonneg N))
    (realDeterminant_factorial_sq_one_le N)

theorem realDeterminantPrefactor_le_power {N : ℕ} (hN : 0 < N) :
    realDeterminantPrefactor N ≤
      (2 * (1 + 10 * Real.exp 12 + 3 / 2) * (n N : ℝ)) ^ n N := by
  let A : ℝ := 1 + 10 * Real.exp 12 + 3 / 2
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA32 : (3 / 2 : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [Real.exp_pos (12 : ℝ)]
  have hn1 : (1 : ℝ) ≤ n N := by
    exact_mod_cast (show 1 ≤ n N by unfold n; omega)
  have hn0 : (0 : ℝ) ≤ n N := Nat.cast_nonneg _
  have hbase : 1 + 10 * Real.exp 12 * (n N : ℝ) ≤ A * (n N : ℝ) := by
    dsimp [A]
    nlinarith only [hn1]
  have hfirst : (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N ≤
      (A * (n N : ℝ)) ^ n N :=
    pow_le_pow_left₀ (by positivity) hbase _
  have hrealpow : (n N : ℝ) ^ ((n N : ℝ) / 2) ≤ (n N : ℝ) ^ n N := by
    have hh := Real.rpow_le_rpow_of_exponent_le hn1
      (show (n N : ℝ) / 2 ≤ (n N : ℝ) by linarith)
    simpa only [Real.rpow_natCast] using hh
  have hsecond : (3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) ≤
      (A * (n N : ℝ)) ^ n N := by
    calc
      _ ≤ A ^ n N * (n N : ℝ) ^ n N :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) hA32 _)
          hrealpow (Real.rpow_nonneg hn0 _) (pow_nonneg hA0 _)
      _ = _ := (mul_pow A (n N : ℝ) (n N)).symm
  have hsheet : realDeterminantSheetPrefactor N ≤ (A * (n N : ℝ)) ^ n N :=
    max_le hfirst hsecond
  calc
    realDeterminantPrefactor N ≤ (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N :=
      realDeterminantPrefactor_le_mass_mul_sheet N
    _ ≤ (2 : ℝ) ^ n N * (A * (n N : ℝ)) ^ n N :=
      mul_le_mul_of_nonneg_left hsheet (pow_nonneg (by norm_num) _)
    _ = _ := by
      change (2 : ℝ) ^ n N * (A * (n N : ℝ)) ^ n N =
        (2 * A * (n N : ℝ)) ^ n N
      simp only [mul_pow]
      ring

theorem realDeterminantPrefactor_eventually_le_exp {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      realDeterminantPrefactor N ≤ Real.exp (d * (n N : ℝ) ^ 2) := by
  let B : ℝ := 2 * (1 + 10 * Real.exp 12 + 3 / 2)
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hconst : Tendsto (fun t : ℝ => Real.log B / t) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop _
  have hlimit : Tendsto (fun t : ℝ => (Real.log B + Real.log t) / t)
      atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using hconst.add hlog
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((tendsto_order.mp hlimit).2 d hd)
  obtain ⟨M, hM⟩ := exists_nat_gt T
  refine ⟨M + 1, ?_⟩
  intro N hNlarge
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hMN : M ≤ n N := by unfold n; omega
  have hsmall := hT (n N : ℝ) (hM.le.trans (Nat.cast_le.mpr hMN))
  have hscalar : Real.log B + Real.log (n N : ℝ) ≤ d * (n N : ℝ) :=
    ((div_lt_iff₀ hn).mp hsmall).le
  have hscaled : (n N : ℝ) * (Real.log B + Real.log (n N : ℝ)) ≤
      d * (n N : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hscalar hn.le
    nlinarith only [hh]
  have hlogpower : Real.log ((B * (n N : ℝ)) ^ n N) ≤ d * (n N : ℝ) ^ 2 := by
    rw [Real.log_pow, Real.log_mul hB.ne' hn.ne']
    exact hscaled
  have hpower : realDeterminantPrefactor N ≤ (B * (n N : ℝ)) ^ n N :=
    realDeterminantPrefactor_le_power hN
  exact hpower.trans ((Real.le_exp_log _).trans (Real.exp_le_exp.mpr hlogpower))

end InternalCatalan

end



noncomputable section
open Set Filter
open scoped BigOperators

namespace InternalCatalan

theorem realDeterminant_uniform_exp_dual {lam Bx₁ Bs₁ Bx₂ Bs₂ : ℝ} (hlam : 0 ≤ lam)
    (p₁ v₁ p₂ v₂ : ℕ → ℝ)
    (hp₁ : Summable (fun j => |p₁ j|)) (hv₁ : Summable (fun j => |v₁ j|))
    (hp₂ : Summable (fun j => |p₂ j|)) (hv₂ : Summable (fun j => |v₂ j|))
    (hBx₁ : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 1 lam p₁ v₁ z ≤ Bx₁)
    (hBs₁ : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v₁ z ≤ Bs₁)
    (hBx₂ : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 2 0 p₂ v₂ z ≤ Bx₂)
    (hBs₂ : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v₂ z ≤ Bs₂)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |determinant N| ≤ Real.exp ((n N : ℝ) ^ 2 *
        (max (realEnergyDualConstant 1 p₁ v₁ Bx₁ Bs₁)
          (realEnergyDualConstant 2 p₂ v₂ Bx₂ Bs₂) + d + Real.log 2 / 2)) := by
  have hd2 : 0 < d / 2 := by positivity
  obtain ⟨N₁, h₁⟩ := realEnergyMajorantOne_uniform_exp hlam p₁ v₁ hp₁ hv₁ hBx₁ hBs₁ hd2
  obtain ⟨N₂, h₂⟩ := realEnergyMajorantTwo_uniform_exp p₂ v₂ hp₂ hv₂ hBx₂ hBs₂ hd2
  obtain ⟨N₃, h₃⟩ := realDeterminantPrefactor_eventually_le_exp hd2
  refine ⟨N₁ + N₂ + N₃ + 1, ?_⟩
  intro N hlarge
  have hN : 0 < N := by omega
  let D₁ : ℝ := realEnergyDualConstant 1 p₁ v₁ Bx₁ Bs₁
  let D₂ : ℝ := realEnergyDualConstant 2 p₂ v₂ Bx₂ Bs₂
  let E₁ : ℝ := Real.exp ((n N : ℝ) ^ 2 * (D₁ + d / 2 + Real.log 2 / 2))
  let E₂ : ℝ := Real.exp ((n N : ℝ) ^ 2 * (D₂ + d / 2 + Real.log 2 / 2))
  let E : ℝ := Real.exp ((n N : ℝ) ^ 2 * (max D₁ D₂ + d / 2 + Real.log 2 / 2))
  have hI₁ : ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) →
      realEnergyMajorantOne N x s ≤ E₁ := h₁ N (by omega)
  have hI₂ : ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      ((∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
        ((n N - 1 - 2 * g N : ℕ) : ℝ)) →
      realEnergyMajorantTwo N x s ≤ E₂ := by
    intro x s hx hs hx0 hxi hsi _
    exact h₂ N (by omega) x s hx hs hx0 hxi hsi
  have hdet := abs_determinant_le_of_two_majorant_bounds hN
    (Real.exp_pos _).le (Real.exp_pos _).le hI₁ hI₂
  change |determinant N| ≤ realDeterminantPrefactor N * max E₁ E₂ at hdet
  have hE₁ : E₁ ≤ E := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [le_max_left D₁ D₂]) (sq_nonneg (n N : ℝ))
  have hE₂ : E₂ ≤ E := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [le_max_right D₁ D₂]) (sq_nonneg (n N : ℝ))
  have hE0 : 0 ≤ max E₁ E₂ := (Real.exp_pos _).le.trans (le_max_left _ _)
  calc
    |determinant N| ≤ realDeterminantPrefactor N * max E₁ E₂ := hdet
    _ ≤ Real.exp ((d / 2) * (n N : ℝ) ^ 2) * E :=
      mul_le_mul (h₃ N (by omega)) (max_le hE₁ hE₂) hE0 (Real.exp_pos _).le
    _ = _ := by
      dsimp [E, D₁, D₂]
      rw [← Real.exp_add]
      congr 1
      ring

theorem realDeterminant_eventually_log_dual {lam Bx₁ Bs₁ Bx₂ Bs₂ : ℝ} (hlam : 0 ≤ lam)
    (p₁ v₁ p₂ v₂ : ℕ → ℝ)
    (hp₁ : Summable (fun j => |p₁ j|)) (hv₁ : Summable (fun j => |v₁ j|))
    (hp₂ : Summable (fun j => |p₂ j|)) (hv₂ : Summable (fun j => |v₂ j|))
    (hBx₁ : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 1 lam p₁ v₁ z ≤ Bx₁)
    (hBs₁ : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v₁ z ≤ Bs₁)
    (hBx₂ : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 2 0 p₂ v₂ z ≤ Bx₂)
    (hBs₂ : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v₂ z ≤ Bs₂)
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        max (realEnergyDualConstant 1 p₁ v₁ Bx₁ Bs₁)
          (realEnergyDualConstant 2 p₂ v₂ Bx₂ Bs₂) + d := by
  obtain ⟨M, hM⟩ := realDeterminant_uniform_exp_dual hlam p₁ v₁ p₂ v₂ hp₁ hv₁ hp₂ hv₂
    hBx₁ hBs₁ hBx₂ hBs₂ hd
  filter_upwards [eventually_ge_atTop (M + 1)] with N hNlarge
  intro hdet
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hlog := (Real.log_le_iff_le_exp (abs_pos.mpr hdet)).mpr (hM N (by omega))
  have hnorm : Real.log |determinant N| / (n N : ℝ) ^ 2 ≤
      max (realEnergyDualConstant 1 p₁ v₁ Bx₁ Bs₁)
        (realEnergyDualConstant 2 p₂ v₂ Bx₂ Bs₂) + d + Real.log 2 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    simpa only [mul_comm] using hlog
  linarith only [hnorm]

end InternalCatalan

end



noncomputable section
open Set Filter
open scoped BigOperators

namespace InternalCatalan

theorem realDeterminant_eventually_log_sup_dual {lam : ℝ} (hlam : 0 ≤ lam)
    (p₁ v₁ p₂ v₂ : ℕ → ℝ)
    (hp₁ : Summable (fun j => |p₁ j|)) (hv₁ : Summable (fun j => |v₁ j|))
    (hp₂ : Summable (fun j => |p₂ j|)) (hv₂ : Summable (fun j => |v₂ j|))
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        max (realEnergyDualConstant 1 p₁ v₁
          (realEnergyRowTrialSup 1 lam p₁ v₁) (realEnergyColumnTrialSup v₁))
          (realEnergyDualConstant 2 p₂ v₂
            (realEnergyRowTrialSup 2 0 p₂ v₂) (realEnergyColumnTrialSup v₂)) + d := by
  exact realDeterminant_eventually_log_dual hlam p₁ v₁ p₂ v₂ hp₁ hv₁ hp₂ hv₂
    (fun z hz hz0 => realEnergyRowTrialField_le_sup (by norm_num) hlam p₁ v₁ hp₁ hv₁ hz hz0)
    (fun z hz => realEnergyColumnTrialField_le_sup v₁ hv₁ hz)
    (fun z hz hz0 => realEnergyRowTrialField_le_sup (by norm_num) (le_refl 0) p₂ v₂ hp₂ hv₂ hz hz0)
    (fun z hz => realEnergyColumnTrialField_le_sup v₂ hv₂ hz) hd


theorem realDeterminant_eventually_log_certificate_sup {d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        realDeterminantCertificateSupBound + d := by
  exact realDeterminant_eventually_log_sup_dual barrier_lambdas.2.1
    barrierP1 barrierV1 barrierP2 barrierV2
    barrier_trials_abs_summable.2.2.1 barrier_trials_abs_summable.2.2.2
    barrier_trials_abs_summable.1 barrier_trials_abs_summable.2.1 hd

end InternalCatalan

end



noncomputable section
open Set Filter

namespace InternalCatalan












end InternalCatalan

end

end OAI

end

section
open OAI.InternalCatalan
open Set Filter
open scoped BigOperators

theorem solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        realDeterminantCertificateSupBound + d := by
  first
  | exact @OAI.InternalCatalan.realDeterminant_eventually_log_certificate_sup
  | (apply OAI.InternalCatalan.realDeterminant_eventually_log_certificate_sup <;> assumption)

end
