-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:49:53.329112+00:00
-- url     : https://prove2.me/submissions/8d596a28-155c-4322-ab17-ee2162ceef54

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
import Definitions.Def_OAIQ247J007
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_conductorCompletedL_logDeriv_hasSum_jb247

section
-- module Solutions.OAIQ247_JB.Compat
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- d13f23b's `logDeriv_fun_comp`, the `fun x => f (g x)` form of `logDeriv_comp` (q247 Jacobsthal). -/
theorem _root_.logDeriv_fun_comp {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    [NormedAlgebra 𝕜 𝕜'] {f : 𝕜' → 𝕜'} {g : 𝕜 → 𝕜'} {x : 𝕜} (hf : DifferentiableAt 𝕜' f (g x))
    (hg : DifferentiableAt 𝕜 g x) : logDeriv (fun x => f (g x)) x = logDeriv f (g x) * deriv g x :=
  logDeriv_comp hf hg
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_Divisor
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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

theorem conductorCompletedL_one_sub (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (s : ℂ) :
    conductorCompletedL χ (1 - s) = rootNumber χ * conductorCompletedL χ⁻¹ s := by
  rw [conductorCompletedL, hχ.completedLFunction_one_sub, conductorCompletedL]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  calc
    (q : ℂ) ^ ((1 - s) / 2) *
        ((q : ℂ) ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s) =
      ((q : ℂ) ^ ((1 - s) / 2) * (q : ℂ) ^ (s - 1 / 2)) *
        (rootNumber χ * completedLFunction χ⁻¹ s) := by ring
    _ = (q : ℂ) ^ (s / 2) * (rootNumber χ * completedLFunction χ⁻¹ s) := by
      rw [← Complex.cpow_add _ _ hq]
      congr 2
      ring
    _ = rootNumber χ * ((q : ℂ) ^ (s / 2) * completedLFunction χ⁻¹ s) := by ring

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

theorem conductorCompletedL_logDeriv (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : completedLFunction χ s ≠ 0) :
    logDeriv (conductorCompletedL χ) s =
      Complex.log (q : ℂ) / 2 + logDeriv (completedLFunction χ) s := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℂ) ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hq)
  have hd : HasDerivAt (fun z : ℂ => (q : ℂ) ^ (z / 2))
      ((q : ℂ) ^ (s / 2) * Complex.log (q : ℂ) * (1 / 2)) s := by
    simpa only [id_eq] using
      ((hasDerivAt_id s).div_const (2 : ℂ)).const_cpow (.inl hq)
  have hl : logDeriv (fun z : ℂ => (q : ℂ) ^ (z / 2)) s =
      Complex.log (q : ℂ) / 2 := by
    rw [logDeriv_apply, hd.deriv]
    field_simp
  exact (logDeriv_mul s hpow hs hd.differentiableAt
    (differentiable_completedLFunction hχ s)).trans (congrArg (· + _) hl)

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

theorem conductorCompletedL_analyticOrderAt_eq (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (conductorCompletedL χ) s = analyticOrderAt (completedLFunction χ) s := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have ha : AnalyticAt ℂ (fun z : ℂ => (q : ℂ) ^ (z / 2)) s :=
    ((differentiable_id.div_const (2 : ℂ)).const_cpow (.inl hq)).analyticAt s
  change analyticOrderAt ((fun z : ℂ => (q : ℂ) ^ (z / 2)) * completedLFunction χ) s = _
  rw [analyticOrderAt_mul ha ((differentiable_completedLFunction hχ).analyticAt s),
    ha.analyticOrderAt_eq_zero.mpr (Complex.cpow_ne_zero_iff.mpr (.inl hq)), zero_add]

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

theorem conductorCompletedL_zeroIndex_re_mem_Ioo (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ)) :
    (divisorZeroIndex₀Val p).re ∈ Set.Ioo (0 : ℝ) 1 :=
  completedL_zero_re_mem_Ioo χ hp hχ
    ((conductorCompletedL_zero_iff χ _).mp (conductorCompletedL_zeroIndex_vanishes χ hχ p))

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

end WeightedTorusJets

namespace WeightedTorusJets

theorem reflected_reciprocal_tsum {ι : Type*} (ρ : ι → ℂ) (e : ι ≃ ι)
    (he : ∀ i, ρ (e i) = 1 - ρ i) :
    ∑' i, (1 / ((-1 : ℂ) - ρ i)).re = -∑' i, (1 / ((2 : ℂ) - ρ i)).re := by
  calc
    ∑' i, (1 / ((-1 : ℂ) - ρ i)).re =
        ∑' i, (1 / ((-1 : ℂ) - ρ (e i))).re := (e.tsum_eq _).symm
    _ = ∑' i, -(1 / ((2 : ℂ) - ρ i)).re := by
      apply tsum_congr
      intro i
      rw [he i, show (-1 : ℂ) - (1 - ρ i) = -((2 : ℂ) - ρ i) by ring,
        div_neg, Complex.neg_re]
    _ = -∑' i, (1 / ((2 : ℂ) - ρ i)).re := tsum_neg



open _root_.Complex _root_.Erdos970.Complex DirichletCharacter

theorem primitive_rootNumber_ne_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    rootNumber χ ≠ 0 := by
  intro hroot
  have hzero : completedLFunction χ 2 = 0 := by
    have h := hχ.completedLFunction_one_sub (-1)
    norm_num [hroot] at h
    exact h
  exact completedL_ne_zero_of_one_le_re χ hχ1 (by norm_num) hzero

theorem logDeriv_conductorCompletedL_one_sub {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (s : ℂ) :
    logDeriv (conductorCompletedL χ) (1 - s) =
      -logDeriv (conductorCompletedL χ⁻¹) s := by
  have hfun : (fun z => conductorCompletedL χ (1 - z)) =
      (fun z => rootNumber χ * conductorCompletedL χ⁻¹ z) :=
    funext (conductorCompletedL_one_sub χ hχ)
  have h := congrArg (fun f => logDeriv f s) hfun
  rw [show (fun z => conductorCompletedL χ (1 - z)) =
      conductorCompletedL χ ∘ (fun z => 1 - z) from rfl,
    logDeriv_comp (differentiable_conductorCompletedL χ hχ1 (1 - s))
    (by fun_prop), logDeriv_const_mul s _ (primitive_rootNumber_ne_zero hχ hχ1)] at h
  simpa using congrArg Neg.neg h

theorem analyticOrderAt_conductorCompletedL_one_sub {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (conductorCompletedL χ) (1 - s) =
      analyticOrderAt (conductorCompletedL χ⁻¹) s := by
  have hfun : (fun z => conductorCompletedL χ (1 - z)) =
      (fun z => rootNumber χ * conductorCompletedL χ⁻¹ z) :=
    funext (conductorCompletedL_one_sub χ hχ)
  have hcomp : analyticOrderAt (fun z => conductorCompletedL χ (1 - z)) s =
      analyticOrderAt (conductorCompletedL χ) (1 - s) := by
    simpa only [Function.comp_def] using
      (analyticOrderAt_comp_of_deriv_ne_zero (f := conductorCompletedL χ) (z₀ := s)
        (g := fun z : ℂ => 1 - z) (by fun_prop) (by simp))
  have hconst : analyticOrderAt (fun _ : ℂ => rootNumber χ) s = 0 :=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr (primitive_rootNumber_ne_zero hχ hχ1)
  calc
    analyticOrderAt (conductorCompletedL χ) (1 - s) =
        analyticOrderAt (fun z => rootNumber χ * conductorCompletedL χ⁻¹ z) s :=
      hcomp.symm.trans (congrArg (fun f => analyticOrderAt f s) hfun)
    _ = analyticOrderAt (fun _ : ℂ => rootNumber χ) s +
        analyticOrderAt (conductorCompletedL χ⁻¹) s := by
      exact analyticOrderAt_mul analyticAt_const
        ((differentiable_conductorCompletedL χ⁻¹ (inv_ne_one.mpr hχ1)).analyticAt s)
    _ = analyticOrderAt (conductorCompletedL χ⁻¹) s := by rw [hconst, zero_add]

theorem completed_reciprocal_tsum_reflection {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hquad : χ.IsQuadratic) :
    (∑' j : Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z),
      (1 / ((-1 : ℂ) - j.1)).re) =
      -∑' j : Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z),
        (1 / ((2 : ℂ) - j.1)).re := by
  let e : (Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z)) ≃
      (Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z)) :=
    Equiv.sigmaCongr (Equiv.subLeft (1 : ℂ)) fun z => finCongr (by
      unfold analyticOrderNatAt
      apply congrArg ENat.toNat
      simpa only [hquad.inv, Equiv.subLeft_apply] using
        (analyticOrderAt_conductorCompletedL_one_sub hχ hχ1 z).symm)
  exact reflected_reciprocal_tsum Sigma.fst e (fun _ => rfl)

section RealPart

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

local notation "ZeroIndices" => Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z)

theorem real_logDeriv_conductorCompletedL_eq_tsum
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hquad : χ.IsQuadratic) (B : ℝ)
    (hbase : Summable (fun j : ZeroIndices => (1 / j.1).re))
    (hexp : ∀ x : ℝ, x = -1 ∨ 1 < x →
      HasSum (fun j : ZeroIndices => (1 / ((x : ℂ) - j.1) + 1 / j.1).re)
        ((logDeriv (conductorCompletedL χ) (x : ℂ)).re - B))
    {s : ℝ} (hs : 1 < s) :
    (logDeriv (conductorCompletedL χ) (s : ℂ)).re =
      ∑' j : ZeroIndices, (1 / ((s : ℂ) - j.1)).re := by
  let C : ℝ := ∑' j : ZeroIndices, (1 / j.1).re
  have hsplit (x : ℝ) (hx : x = -1 ∨ 1 < x) :
      (∑' j : ZeroIndices, (1 / ((x : ℂ) - j.1)).re) =
        (logDeriv (conductorCompletedL χ) (x : ℂ)).re - B - C := by
    apply HasSum.tsum_eq
    convert (hexp x hx).sub hbase.hasSum using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    simp only [Complex.add_re, add_sub_cancel_right]
  have hreflection : (logDeriv (conductorCompletedL χ) (-1)).re =
      -(logDeriv (conductorCompletedL χ) 2).re := by
    have h := logDeriv_conductorCompletedL_one_sub hχ hχ1 2
    rw [hquad.inv] at h
    have harg : (1 - (2 : ℂ)) = -1 := by ring
    simpa only [harg, Complex.neg_re] using congrArg Complex.re h
  have hcancel : B + C = 0 := by
    have htwo := hsplit 2 (.inr (by norm_num))
    have hneg := hsplit (-1) (.inl rfl)
    have hzero := completed_reciprocal_tsum_reflection hχ hχ1 hquad
    norm_num only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_one] at htwo hneg
    linarith
  rw [hsplit s (.inr hs)]
  linarith

end RealPart

end WeightedTorusJets

namespace RealCharacterAnalysis

open _root_.Complex _root_.Erdos970.Complex _root_.Erdos970.Complex.Hadamard

theorem divisorIndexEquivAnalytic_val {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (p : divisorZeroIndex₀ f Set.univ) :
    (divisorIndexEquivAnalytic hf h0 p).1 = divisorZeroIndex₀Val p := rfl

theorem tsum_divisorIndex_eq_analytic {E : Type*} [NormedAddCommGroup E] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (F : ℂ → E) :
    (∑' p : divisorZeroIndex₀ f Set.univ, F (divisorZeroIndex₀Val p)) =
      ∑' p : Σ z : ℂ, Fin (analyticOrderNatAt f z), F p.1 := by
  simpa only [Function.comp_def, divisorIndexEquivAnalytic_val] using
    (divisorIndexEquivAnalytic hf h0).tsum_eq (fun p => F p.1)

theorem summable_divisorIndex_iff_analytic {E : Type*} [NormedAddCommGroup E] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (F : ℂ → E) :
    Summable (fun p : divisorZeroIndex₀ f Set.univ => F (divisorZeroIndex₀Val p)) ↔
      Summable (fun p : Σ z : ℂ, Fin (analyticOrderNatAt f z) => F p.1) := by
  simpa only [Function.comp_def, divisorIndexEquivAnalytic_val] using
    (divisorIndexEquivAnalytic hf h0).summable_iff (f := fun p => F p.1)

end RealCharacterAnalysis

end
end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_E
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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

open _root_.Complex _root_.Filter
open scoped Topology ComplexConjugate

namespace RealCharacterAnalysis

theorem real_values_iff_quadratic {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (∀ a : ZMod q, (χ a).im = 0) ↔ χ.IsQuadratic := by
  constructor
  · intro h
    have hc : star χ = χ := by
      ext a
      exact Complex.conj_eq_iff_im.mpr (h a)
    have hi : χ⁻¹ = χ := (MulChar.star_eq_inv χ).symm.trans hc
    apply MulChar.isQuadratic_iff_sq_eq_one.mpr
    calc
      χ ^ 2 = χ * χ := sq χ
      _ = χ * χ⁻¹ := congrArg (χ * ·) hi.symm
      _ = 1 := mul_inv_cancel χ
  · intro h a
    rcases h a with h | h | h <;> simp [h]

theorem lSeries_conj (f : ℕ → ℂ) (s : ℂ) :
    LSeries (fun n => conj (f n)) (conj s) = conj (LSeries f s) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp only [LSeries.term_of_ne_zero hn, map_div₀]
    rw [Complex.cpow_conj _ _ (by simp [Real.pi_ne_zero.symm])]
    simp

theorem lFunction_conj {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ (conj s) =
      conj (DirichletCharacter.LFunction χ s) := by
  have hi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hf := DirichletCharacter.differentiable_LFunction hi
  have hg : Differentiable ℂ
      (conj ∘ DirichletCharacter.LFunction χ ∘ conj) := by
    intro z
    simpa using
      (DirichletCharacter.differentiable_LFunction hχ (conj z)).conj_conj
  have heq : DirichletCharacter.LFunction χ⁻¹ =
      conj ∘ DirichletCharacter.LFunction χ ∘ conj := by
    apply (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      (hg.differentiableOn.analyticOnNhd isOpen_univ)
    have hn : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    simp only [Function.comp_apply]
    rw [DirichletCharacter.LFunction_eq_LSeries χ⁻¹ hz,
      DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hz)]
    have hc : (fun n : ℕ => χ⁻¹ (n : ZMod q)) =
        (fun n : ℕ => conj (χ (n : ZMod q))) := by
      funext n
      simpa using (MulChar.star_apply' χ (n : ZMod q)).symm
    rw [hc, ← lSeries_conj, Complex.conj_conj]
  simpa using congrFun heq (conj s)

end RealCharacterAnalysis
end

end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_RealLogDerivConductorCompletedLDivisorTsum
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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

open _root_.Erdos970.Complex DirichletCharacter _root_.Erdos970.Complex.Hadamard RealCharacterAnalysis

section

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

local notation "DivisorIndices" => divisorZeroIndex₀ (conductorCompletedL χ) Set.univ

theorem real_logDeriv_conductorCompletedL_eq_divisor_tsum
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hquad : χ.IsQuadratic) (B : ℂ)
    (hbase : Summable (fun j : DivisorIndices => (1 / divisorZeroIndex₀Val j).re))
    (hexp : ∀ z : ℂ, conductorCompletedL χ z ≠ 0 →
      HasSum (fun j : DivisorIndices =>
        1 / (z - divisorZeroIndex₀Val j) + 1 / divisorZeroIndex₀Val j)
        (logDeriv (conductorCompletedL χ) z - B))
    {s : ℝ} (hs : 1 < s) :
    (logDeriv (conductorCompletedL χ) (s : ℂ)).re =
      ∑' j : DivisorIndices, (1 / ((s : ℂ) - divisorZeroIndex₀Val j)).re := by
  have hf := differentiable_conductorCompletedL χ hχ1
  have h0 := conductorCompletedL_ne_zero_at_zero χ hχ hχ1
  have hnz (x : ℝ) (hx : x = -1 ∨ 1 < x) : conductorCompletedL χ (x : ℂ) ≠ 0 := by
    intro hzero
    have hstrip := completedL_zero_re_mem_Ioo χ hχ hχ1
      ((conductorCompletedL_zero_iff χ (x : ℂ)).mp hzero)
    simp only [Set.mem_Ioo, Complex.ofReal_re] at hstrip
    rcases hx with rfl | hx
    · linarith
    · linarith
  rw [tsum_divisorIndex_eq_analytic hf h0 (fun z => (1 / ((s : ℂ) - z)).re)]
  apply real_logDeriv_conductorCompletedL_eq_tsum hχ hχ1 hquad B.re
    ((summable_divisorIndex_iff_analytic hf h0 (fun z => (1 / z).re)).mp hbase) _ hs
  intro x hx
  apply ((divisorIndexEquivAnalytic hf h0).hasSum_iff
    (f := fun j => (1 / ((x : ℂ) - j.1) + 1 / j.1).re)).mp
  simpa only [Function.comp_def, divisorIndexEquivAnalytic_val, Complex.sub_re] using
    Complex.hasSum_re (hexp (x : ℂ) (hnz x hx))

end

end WeightedTorusJets

namespace WeightedTorusJets

theorem abs_reciprocal_sub_re_le_normSq {ρ : ℂ} {s : ℝ}
    (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) (hs : 1 < s) :
    |(1 / ((s : ℂ) - ρ)).re| ≤
      (s * (1 + 1 / (s - 1) ^ 2)) / Complex.normSq ρ := by
  have hs₀ : 0 < s := zero_lt_one.trans hs
  have hsquare : 0 < (s - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hρne : ρ ≠ 0 := by
    intro h
    simp [h] at hρ₀
  have hnorm : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hρne
  have hdenlower : (s - 1) ^ 2 ≤ Complex.normSq ((s : ℂ) - ρ) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, zero_sub]
    nlinarith [sq_nonneg ρ.im, mul_self_le_mul_self
      (show 0 ≤ s - 1 by linarith) (show s - 1 ≤ s - ρ.re by linarith)]
  have hden : 0 < Complex.normSq ((s : ℂ) - ρ) := hsquare.trans_le hdenlower
  have hnormadd : Complex.normSq ρ ≤ 1 + Complex.normSq ((s : ℂ) - ρ) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, zero_sub]
    nlinarith [sq_nonneg (s - ρ.re), mul_self_le_mul_self hρ₀.le hρ₁.le]
  have hone : 1 ≤ Complex.normSq ((s : ℂ) - ρ) / (s - 1) ^ 2 := by
    exact (le_div_iff₀ hsquare).mpr (by simpa using hdenlower)
  have hbound : Complex.normSq ρ ≤
      (1 + 1 / (s - 1) ^ 2) * Complex.normSq ((s : ℂ) - ρ) := by
    calc
      Complex.normSq ρ ≤ 1 + Complex.normSq ((s : ℂ) - ρ) := hnormadd
      _ ≤ Complex.normSq ((s : ℂ) - ρ) / (s - 1) ^ 2 +
          Complex.normSq ((s : ℂ) - ρ) := by linarith
      _ = _ := by ring
  have hnum : 0 ≤ s - ρ.re := by linarith
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
  rw [abs_of_nonneg (div_nonneg hnum hden.le)]
  apply (div_le_div_iff₀ hden hnorm).mpr
  calc
    (s - ρ.re) * Complex.normSq ρ ≤ s * Complex.normSq ρ :=
      mul_le_mul_of_nonneg_right (sub_le_self s hρ₀.le) hnorm.le
    _ ≤ s * ((1 + 1 / (s - 1) ^ 2) * Complex.normSq ((s : ℂ) - ρ)) :=
      mul_le_mul_of_nonneg_left hbound hs₀.le
    _ = _ := by ring

theorem abs_reciprocal_re_le_normSq {ρ : ℂ}
    (hρ₀ : 0 ≤ ρ.re) (hρ₁ : ρ.re ≤ 1) :
    |(1 / ρ).re| ≤ 1 / Complex.normSq ρ := by
  simp only [one_div, Complex.inv_re]
  rw [abs_of_nonneg (div_nonneg hρ₀ (Complex.normSq_nonneg ρ))]
  simpa only [one_div] using div_le_div_of_nonneg_right hρ₁ (Complex.normSq_nonneg ρ)

theorem summable_abs_reciprocal_sub_re {ι : Type*} (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (hsum : Summable (fun i => ‖ρ i‖⁻¹ ^ (2 : ℕ)))
    {s : ℝ} (hs : 1 < s) :
    Summable (fun i => |(1 / ((s : ℂ) - ρ i)).re|) := by
  have hnormSq : Summable (fun i => 1 / Complex.normSq (ρ i)) := by
    simpa only [Complex.normSq_eq_norm_sq, one_div, inv_pow] using hsum
  apply (hnormSq.mul_left (s * (1 + 1 / (s - 1) ^ 2))).of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs, abs_abs, mul_one_div] using
    abs_reciprocal_sub_re_le_normSq (hstrip i).1 (hstrip i).2 hs

theorem summable_abs_reciprocal_re {ι : Type*} (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hsum : Summable (fun i => ‖ρ i‖⁻¹ ^ (2 : ℕ))) :
    Summable (fun i => |(1 / ρ i).re|) := by
  have hnormSq : Summable (fun i => 1 / Complex.normSq (ρ i)) := by
    simpa only [Complex.normSq_eq_norm_sq, one_div, inv_pow] using hsum
  apply hnormSq.of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs, abs_abs] using
    abs_reciprocal_re_le_normSq (hstrip i).1 (hstrip i).2



open _root_.Erdos970.Complex.Hadamard

theorem divisorZeroIndex_val_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (p : divisorZeroIndex₀ f Set.univ) : f (divisorZeroIndex₀Val p) = 0 := by
  by_contra hz
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hzero := (hf.analyticAt (divisorZeroIndex₀Val p)).analyticOrderAt_eq_zero.mpr hz
  have hsupport := divisorZeroIndex₀Val_mem_divisor_support p
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ _), hzero] at hsupport
  simp at hsupport

theorem conductorCompletedL_divisorIndex_re_mem_Ioo {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ₁ : χ ≠ 1)
    (p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ) :
    0 < (divisorZeroIndex₀Val p).re ∧ (divisorZeroIndex₀Val p).re < 1 := by
  have hzero := divisorZeroIndex_val_zero (differentiable_conductorCompletedL χ hχ₁) p
  exact completedL_zero_re_mem_Ioo χ hχ hχ₁
    ((conductorCompletedL_zero_iff χ _).mp hzero)

theorem conductorCompletedL_abs_reciprocal_summable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ₁ : χ ≠ 1)
    (hsum : Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (2 : ℕ)))
    {s : ℝ} (hs : 1 < s) :
    Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ =>
      |(1 / ((s : ℂ) - divisorZeroIndex₀Val p)).re|) ∧
    Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ =>
      |(1 / divisorZeroIndex₀Val p).re|) := by
  have hstrip := conductorCompletedL_divisorIndex_re_mem_Ioo χ hχ hχ₁
  exact ⟨summable_abs_reciprocal_sub_re _ hstrip hsum hs,
    summable_abs_reciprocal_re _ (fun p => ⟨(hstrip p).1.le, (hstrip p).2.le⟩) hsum⟩

theorem exists_divisorZeroIndex_val_eq_of_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfne : f ≠ 0) {z : ℂ} (hz₀ : z ≠ 0) (hz : f z = 0) :
    ∃ p : divisorZeroIndex₀ f Set.univ, divisorZeroIndex₀Val p = z := by
  have horder : analyticOrderAt f z ≠ 0 := (hf.analyticAt z).analyticOrderAt_ne_zero.mpr hz
  have htop : analyticOrderAt f z ≠ ⊤ := by
    exact fun h => hfne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hf.analyticAt).mp h)
  have hpos : 0 < analyticOrderNatAt f z := by
    rw [Nat.pos_iff_ne_zero, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
    exact ⟨horder, htop⟩
  refine ⟨⟨⟨z, ⟨0, ?_⟩⟩, hz₀⟩, rfl⟩
  rw [RealCharacterAnalysis.toNat_divisor_eq_analyticOrderNatAt hf]
  exact hpos

end WeightedTorusJets
namespace WeightedTorusJets

open _root_.Erdos970.Complex DirichletCharacter _root_.Erdos970.Complex.Hadamard

theorem conductorCompletedL_zero_sum_absolutely_summable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ =>
      |(1 / ((s : ℂ) - divisorZeroIndex₀Val p)).re|) :=
  (conductorCompletedL_abs_reciprocal_summable χ hχ hχ1
    (conductorCompletedL_zeroIndex_summable_inv_sq χ hχ hχ1) hs).1

theorem real_logDeriv_conductorCompletedL_eq_divisor_tsum_source {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hquad : χ.IsQuadratic) {s : ℝ} (hs : 1 < s) :
    (logDeriv (conductorCompletedL χ) (s : ℂ)).re =
      ∑' p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ,
        (1 / ((s : ℂ) - divisorZeroIndex₀Val p)).re := by
  obtain ⟨B, hB⟩ := conductorCompletedL_logDeriv_hasSum_jb247 χ hχ hχ1
  apply real_logDeriv_conductorCompletedL_eq_divisor_tsum hχ hχ1 hquad B _ hB hs
  exact (summable_abs_reciprocal_re divisorZeroIndex₀Val
    (fun p => let h := conductorCompletedL_zeroIndex_re_mem_Ioo χ hχ hχ1 p
      ⟨h.1.le, h.2.le⟩)
    (conductorCompletedL_zeroIndex_summable_inv_sq χ hχ hχ1)).of_abs

end WeightedTorusJets

end
section

open _root_.Filter _root_.Set
open scoped Topology

namespace WeightedTorusJets

lemma analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gamma s := by
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hzpos : 0 < z.re := hz
    linarith
  exact hd.analyticAt ((Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs)

theorem exists_bound_Gamma_logDeriv_parity :
    ∃ C : ℝ, 0 < C ∧ ∀ s ε : ℝ, 1 < s → s ≤ 2 → (ε = 0 ∨ ε = 1) →
      ‖logDeriv Complex.Gamma (((s + ε) / 2 : ℝ) : ℂ)‖ ≤ C := by
  have hc : ContinuousOn (fun t : ℝ ↦ logDeriv Complex.Gamma (t : ℂ))
      (Icc (1 / 2) (3 / 2)) := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have ha := analyticAt_Gamma_of_re_pos (s := (t : ℂ)) (by simpa using htpos)
    exact ((ha.deriv.continuousAt.div ha.continuousAt
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using htpos))).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s ε hs hs2 hε
  apply (hC ((s + ε) / 2) ?_).trans (le_max_left _ _)
  rcases hε with rfl | rfl <;> constructor <;> linarith

end WeightedTorusJets

end
section

open scoped Classical

namespace WeightedTorusJets

theorem character_parity_parameter_real {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (1 - (χ (-1)).re) / 2 = if χ.Even then (0 : ℝ) else 1 := by
  rcases χ.even_or_odd with h | h
  · simp [h, show χ (-1) = 1 from h]
  · simp [h.not_even, show χ (-1) = -1 from h]

end WeightedTorusJets

end
section
namespace WeightedTorusJets

theorem logDeriv_GammaR_add {s a : ℂ} (hs : 0 < (s + a).re) :
    logDeriv (fun z : ℂ => Complex.Gammaℝ (z + a)) s =
      -Complex.log (Real.pi : ℂ) / 2 + logDeriv Complex.Gamma ((s + a) / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp : (Real.pi : ℂ) ^ (-(s + a) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl hpi)
  have hgpos : 0 < ((s + a) / 2).re := by
    simpa only [Complex.div_ofNat_re] using half_pos hs
  have hg := (analyticAt_Gamma_of_re_pos hgpos).differentiableAt
  have hgn : Complex.Gamma ((s + a) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hgpos
  have hpow : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + a) / 2))
      ((Real.pi : ℂ) ^ (-(s + a) / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    simpa only [id_eq, Pi.neg_apply] using
      (((hasDerivAt_id s).add_const a).neg.div_const (2 : ℂ)).const_cpow (Or.inl hpi)
  have harg : HasDerivAt (fun z : ℂ => (z + a) / 2) (1 / 2) s :=
    ((hasDerivAt_id s).add_const a).div_const (2 : ℂ)
  change logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + a) / 2) *
    Complex.Gamma ((z + a) / 2)) s = _
  rw [logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-(z + a) / 2))
    (g := fun z : ℂ => Complex.Gamma ((z + a) / 2)) s hp hgn hpow.differentiableAt
      (hg.comp s harg.differentiableAt)]
  rw [logDeriv_apply, hpow.deriv]
  rw [logDeriv_fun_comp (f := Complex.Gamma) (g := fun z : ℂ => (z + a) / 2)
    hg harg.differentiableAt, harg.deriv]
  field_simp

theorem gammaFactor_logDeriv_real_parity {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℝ} (hs : 0 < s) :
    logDeriv χ.gammaFactor (s : ℂ) =
      -Complex.log (Real.pi : ℂ) / 2 +
        logDeriv Complex.Gamma (((s + (1 - (χ (-1)).re) / 2) / 2 : ℝ) : ℂ) / 2 := by
  classical
  rw [character_parity_parameter_real]
  by_cases hχ : χ.Even
  · have hf : χ.gammaFactor = Complex.Gammaℝ := funext hχ.gammaFactor_def
    rw [hf]
    simpa only [hχ, ite_true, if_true, add_zero, Complex.ofReal_div, Complex.ofReal_ofNat] using
      logDeriv_GammaR_add (s := (s : ℂ)) (a := 0) (by simpa using hs)
  · have hf : χ.gammaFactor = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z
      simp [DirichletCharacter.gammaFactor, hχ]
    rw [hf]
    simpa only [hχ, ite_false, if_false, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_ofNat] using
      logDeriv_GammaR_add (s := (s : ℂ)) (a := 1) (by simp <;> linarith)

theorem exists_bound_gammaFactor_logDeriv :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∀ s : ℝ, 1 < s → s ≤ 2 → ‖logDeriv χ.gammaFactor (s : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_Gamma_logDeriv_parity
  refine ⟨‖Complex.log (Real.pi : ℂ)‖ / 2 + C / 2, by positivity, ?_⟩
  intro q χ s hs hs2
  have heps : (1 - (χ (-1)).re) / 2 = 0 ∨ (1 - (χ (-1)).re) / 2 = 1 := by
    rw [character_parity_parameter_real]
    split_ifs <;> simp
  have hg := hbound s ((1 - (χ (-1)).re) / 2) hs hs2 heps
  rw [gammaFactor_logDeriv_real_parity χ (by linarith)]
  calc
    _ ≤ ‖-Complex.log (Real.pi : ℂ) / 2‖ +
        ‖logDeriv Complex.Gamma (((s + (1 - (χ (-1)).re) / 2) / 2 : ℝ) : ℂ) / 2‖ :=
      norm_add_le _ _
    _ = ‖Complex.log (Real.pi : ℂ)‖ / 2 +
        ‖logDeriv Complex.Gamma (((s + (1 - (χ (-1)).re) / 2) / 2 : ℝ) : ℂ)‖ / 2 := by
      simp only [norm_div, norm_neg, Complex.norm_ofNat]
    _ ≤ _ := by linarith

theorem exists_upper_bound_conductor_gammaFactor_logDeriv :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ), 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
      ∀ s : ℝ, 1 < s → s ≤ 2 →
      (Complex.log (q : ℂ) / 2 + logDeriv χ.gammaFactor (s : ℂ)).re ≤
        K * Real.log q := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_gammaFactor_logDeriv
  refine ⟨C + 1, by linarith, ?_⟩
  intro q hq χ s hs hs2
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 1 < Real.log q :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hg : (logDeriv χ.gammaFactor (s : ℂ)).re ≤ C :=
    (Complex.re_le_norm _).trans (hbound q χ s hs hs2)
  rw [Complex.add_re, Complex.div_ofNat_re, ← Complex.ofReal_natCast,
    Complex.log_ofReal_re]
  nlinarith

end WeightedTorusJets
end
section

open _root_.Filter _root_.Set
open scoped Topology

namespace WeightedTorusJets

lemma riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hne
  · simp
  · intro hz
    have h := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_eq_inv_sub_mul hne, hz, mul_zero] at h
    exact h rfl

lemma logDeriv_riemannZeta₁ {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta₁ s = 1 / (s - 1) + logDeriv riemannZeta s := by
  have hne : s ≠ 1 := by intro h; simp [h] at hs
  have hz := riemannZeta₁_ne_zero_of_one_le_re hs.le
  rw [logDeriv_apply, logDeriv_apply,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hne, riemannZeta_eq_inv_sub_mul hne]
  field_simp
  ring

theorem exists_bound_zeta_logDeriv :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖-logDeriv riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1)‖ ≤ C := by
  have hc : ContinuousOn (fun s : ℝ ↦ logDeriv riemannZeta₁ (s : ℂ)) (Icc 1 2) := by
    intro s hs
    have ha := differentiable_riemannZeta₁.analyticAt (s : ℂ)
    exact ((ha.deriv.continuousAt.div ha.continuousAt
      (riemannZeta₁_ne_zero_of_one_le_re (by simpa using hs.1))).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s hs hs2
  have heq : -logDeriv riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1) =
      -logDeriv riemannZeta₁ (s : ℂ) := by
    rw [logDeriv_riemannZeta₁ (by simpa using hs)]
    ring
  rw [heq, norm_neg]
  exact (hC s ⟨hs.le, hs2⟩).trans (le_max_left _ _)

theorem exists_upper_bound_zeta_logDeriv_re :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      (-logDeriv riemannZeta (s : ℂ)).re ≤ 1 / (s - 1) + C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_zeta_logDeriv
  refine ⟨C, hC, ?_⟩
  intro s hs hs2
  have h := (Complex.re_le_norm _).trans (hbound s hs hs2)
  have heq : (1 / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
      Complex.ofReal_re]
  rw [Complex.sub_re, heq] at h
  linarith

end WeightedTorusJets
end
section
namespace WeightedTorusJets

theorem conductorCompletedL_logDeriv_decomposition {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (conductorCompletedL χ) s = logDeriv (DirichletCharacter.LFunction χ) s +
      (Complex.log (q : ℂ) / 2 + logDeriv χ.gammaFactor s) := by
  classical
  have hs0 : 0 < s.re := by linarith
  have hgn := gammaFactor_ne_zero_of_re_pos χ hs0
  have hinv : Differentiable ℂ (fun z => (χ.gammaFactor z)⁻¹) := by
    rcases χ.even_or_odd with heven | hodd
    · convert Complex.differentiable_Gammaℝ_inv using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      rw [heven.gammaFactor_def]
    · convert Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1) using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      rw [hodd.gammaFactor_def]
      rfl
  have hgamma : DifferentiableAt ℂ χ.gammaFactor s := by
    convert (hinv s).inv (inv_ne_zero hgn) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact (inv_inv (χ.gammaFactor z)).symm
  have heq : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      fun z => DirichletCharacter.LFunction χ z * χ.gammaFactor z := by
    have hU : {z : ℂ | 0 < z.re} ∈ nhds s :=
      (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs0
    filter_upwards [hU] with z hz using completedL_eq_mul_gammaFactor χ hz
  have hl := (logDeriv_congr_nhds heq).eq_of_nhds
  rw [conductorCompletedL_logDeriv χ hχ
    (completedL_ne_zero_of_one_le_re χ hχ hs.le), hl]
  rw [logDeriv_mul s
    (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs.le) hgn
    (DirichletCharacter.differentiable_LFunction hχ s) hgamma]
  ring

end WeightedTorusJets
end

end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_SumLogPrimeFactors
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

namespace WeightedTorusJets

theorem completedL_analyticOrderAt_eq_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) s =
      analyticOrderAt (DirichletCharacter.LFunction χ) s := by
  have hgn := gammaFactor_ne_zero_of_re_pos χ hs
  have hinv : Differentiable ℂ (fun z => (χ.gammaFactor z)⁻¹) := by
    rcases χ.even_or_odd with heven | hodd
    · convert Complex.differentiable_Gammaℝ_inv using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      rw [heven.gammaFactor_def]
    · convert Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1) using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      rw [hodd.gammaFactor_def]
      rfl
  have hgamma : AnalyticAt ℂ χ.gammaFactor s := by
    convert (hinv.analyticAt s).inv (inv_ne_zero hgn) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact (inv_inv (χ.gammaFactor z)).symm
  have heq : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      fun z => DirichletCharacter.LFunction χ z * χ.gammaFactor z := by
    have hU : {z : ℂ | 0 < z.re} ∈ nhds s :=
      (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs
    filter_upwards [hU] with z hz using completedL_eq_mul_gammaFactor χ hz
  rw [analyticOrderAt_congr heq]
  change analyticOrderAt (DirichletCharacter.LFunction χ * χ.gammaFactor) s = _
  rw [analyticOrderAt_mul ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s) hgamma,
    hgamma.analyticOrderAt_eq_zero.mpr hgn, add_zero]

theorem conductorCompletedL_analyticOrderAt_eq_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (conductorCompletedL χ) s =
      analyticOrderAt (DirichletCharacter.LFunction χ) s :=
  (conductorCompletedL_analyticOrderAt_eq χ hχ s).trans
    (completedL_analyticOrderAt_eq_LFunction χ hχ hs)



end WeightedTorusJets

end AnalyticAssemblyScope

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_NormLogDerivLFunctionNegLogDerivZeta
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace WeightedTorusJets
open _root_.ArithmeticFunction DirichletCharacter
open scoped LSeries.notation BigOperators ComplexOrder
theorem norm_logDeriv_LFunction_le_neg_logDeriv_zeta {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
      (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re := by
  have htw := LSeriesSummable_twist_vonMangoldt χ hs
  have hΛ := LSeriesSummable_vonMangoldt (show 1 < (s.re : ℂ).re from hs)
  calc
    ‖deriv (LFunction χ) s / LFunction χ s‖ = ‖LSeries (↗χ * ↗Λ) s‖ := by
      rw [LSeries_twist_vonMangoldt_eq χ hs,
        deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
      simp [neg_div]
    _ ≤ ∑' n, ‖LSeries.term (↗χ * ↗Λ) s n‖ := norm_tsum_le_tsum_norm htw.norm
    _ ≤ ∑' n, ‖LSeries.term ↗Λ (s.re : ℂ) n‖ := by
      apply htw.norm.tsum_le_tsum _ hΛ.norm
      intro n
      have hcoeff : ‖(↗χ * ↗Λ) n‖ ≤ ‖(↗Λ n : ℂ)‖ := by
        simpa using mul_le_of_le_one_left (norm_nonneg (vonMangoldt n : ℂ))
          (χ.norm_le_one (n : ZMod q))
      simpa only [LSeries.norm_term_eq, Complex.ofReal_re] using
        (LSeries.norm_term_le (f := ↗χ * ↗Λ) (g := ↗Λ) (n := n) s hcoeff)
    _ = (LSeries ↗Λ (s.re : ℂ)).re := by
      rw [LSeries, Complex.re_tsum hΛ]
      apply tsum_congr
      intro n
      have hn : 0 ≤ LSeries.term ↗Λ (s.re : ℂ) n :=
        LSeries.term_nonneg (by exact_mod_cast (vonMangoldt_nonneg (n := n))) s.re
      simpa using congrArg Complex.re (RCLike.norm_of_nonneg' hn)
    _ = (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re :=
      congrArg Complex.re (LSeries_vonMangoldt_eq_deriv_riemannZeta_div (show 1 < (s.re : ℂ).re from hs))

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.Erdos970.Complex DirichletCharacter _root_.Erdos970.Complex.Hadamard

theorem exists_upper_bound_completedL_logDeriv :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ s : ℝ, 1 < s → s ≤ 2 →
      (logDeriv (conductorCompletedL χ) (s : ℂ)).re ≤
        1 / (s - 1) + K * Real.log q := by
  obtain ⟨Kg, hKg, hg⟩ := exists_upper_bound_conductor_gammaFactor_logDeriv
  obtain ⟨Cz, hCz, hz⟩ := exists_upper_bound_zeta_logDeriv_re
  refine ⟨Kg + Cz, by positivity, ?_⟩
  intro q _ hq χ hχ s hs hs2
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 1 < Real.log q :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hnorm := norm_logDeriv_LFunction_le_neg_logDeriv_zeta χ
    (s := (s : ℂ)) (by simpa using hs)
  have hL : (logDeriv (LFunction χ) (s : ℂ)).re ≤
      (-logDeriv riemannZeta (s : ℂ)).re := by
    simpa only [logDeriv_apply, Complex.ofReal_re, neg_div] using
      (Complex.re_le_norm (deriv (LFunction χ) (s : ℂ) / LFunction χ (s : ℂ))).trans hnorm
  have hdecomp := congrArg Complex.re
    (conductorCompletedL_logDeriv_decomposition χ hχ (s := (s : ℂ))
      (by simpa using hs))
  rw [Complex.add_re] at hdecomp
  have hgamma := hg q hq χ s hs hs2
  have hzeta := hz s hs hs2
  nlinarith

theorem reciprocal_re_lower_of_near_one {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hzre : z.re ≤ 1) (hz : ‖z - 1‖ ≤ r) :
    1 / (6 * r) ≤ (1 / (((1 + 4 * r : ℝ) : ℂ) - z)).re := by
  have hre := (Complex.abs_re_le_norm (z - 1)).trans hz
  have him := (Complex.abs_im_le_norm (z - 1)).trans hz
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    sub_zero] at hre him
  have hu : 4 * r ≤ 1 + 4 * r - z.re := by linarith
  have hu' : 1 + 4 * r - z.re ≤ 5 * r := by
    have := (abs_le.mp hre).1
    linarith
  have him2 : z.im ^ 2 ≤ r ^ 2 := by
    exact sq_le_sq.mpr (by simpa only [abs_of_pos hr] using him)
  have hden : 0 < (1 + 4 * r - z.re) ^ 2 + z.im ^ 2 := by
    nlinarith [sq_pos_of_pos (by linarith : 0 < 1 + 4 * r - z.re), sq_nonneg z.im]
  have hcomp : (1 + 4 * r - z.re) ^ 2 + z.im ^ 2 ≤
      6 * r * (1 + 4 * r - z.re) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu') (by linarith : 0 ≤ 1 + 4 * r - z.re)]
  have hdiv : 1 / (6 * r) ≤ (1 + 4 * r - z.re) /
      ((1 + 4 * r - z.re) ^ 2 + z.im ^ 2) :=
    (div_le_div_iff₀ (by positivity) hden).mpr (by nlinarith)
  simpa only [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re,
    Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_mul_neg,
    pow_two] using hdiv

theorem near_one_indices_eq_of_tsum_bound {ι : Type*} (z : ι → ℂ)
    {r B : ℝ} (hr : 0 < r) (hB : r * B < 1 / 12)
    (hre : ∀ i, (z i).re ≤ 1)
    (hsum : Summable (fun i => (1 / (((1 + 4 * r : ℝ) : ℂ) - z i)).re))
    (hbound : (∑' i, (1 / (((1 + 4 * r : ℝ) : ℂ) - z i)).re) ≤
      1 / (4 * r) + B)
    {i j : ι} (hi : ‖z i - 1‖ ≤ r) (hj : ‖z j - 1‖ ≤ r) : i = j := by
  classical
  by_contra hij
  have hnonneg : ∀ k, 0 ≤ (1 / (((1 + 4 * r : ℝ) : ℂ) - z k)).re := by
    intro k
    simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
    exact div_nonneg (by have := hre k; linarith) (Complex.normSq_nonneg _)
  have htwo := hsum.sum_le_tsum {i, j} (fun k _ => hnonneg k)
  simp only [Finset.sum_pair hij] at htwo
  have hi' := reciprocal_re_lower_of_near_one hr (hre i) hi
  have hj' := reciprocal_re_lower_of_near_one hr (hre j) hj
  have hle : 2 / (6 * r) ≤ 1 / (4 * r) + B := by
    rw [show 2 / (6 * r) = 1 / (6 * r) + 1 / (6 * r) by ring]
    linarith
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hcalc : r * (2 / (6 * r)) = 1 / 3 := by field_simp <;> ring
  have hcalc' : r * (1 / (4 * r) + B) = 1 / 4 + r * B := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hle hr.le
  rw [hcalc, hcalc'] at hmul
  linarith

theorem exists_near_one_divisor_indices_unique :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 4 ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 → χ.IsQuadratic →
      ∀ i j : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ,
      ‖divisorZeroIndex₀Val i - 1‖ ≤ c / Real.log q →
      ‖divisorZeroIndex₀Val j - 1‖ ≤ c / Real.log q → i = j := by
  obtain ⟨K, hK, hupper⟩ := exists_upper_bound_completedL_logDeriv
  let c : ℝ := 1 / (24 * (K + 1))
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hc4 : c < 1 / 4 := by
    dsimp [c]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  refine ⟨c, hc, hc4, ?_⟩
  intro q _ hq χ hprim hχ hquad i j hi hj
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 1 < Real.log q :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  let r : ℝ := c / Real.log q
  have hr : 0 < r := div_pos hc (by linarith)
  have hr4 : r < 1 / 4 := by
    apply lt_trans (b := c)
    · exact (div_lt_self hc hlogq)
    · exact hc4
  have hKc : c * K < 1 / 12 := by
    dsimp [c]
    rw [div_mul_eq_mul_div, (div_lt_iff₀ (by positivity))]
    nlinarith
  have hBr : r * (K * Real.log q) < 1 / 12 := by
    have heq : r * (K * Real.log q) = c * K := by
      dsimp [r]
      field_simp
    rwa [heq]
  have hs : 1 < 1 + 4 * r := by linarith
  have hs2 : 1 + 4 * r ≤ 2 := by linarith
  apply near_one_indices_eq_of_tsum_bound divisorZeroIndex₀Val hr hBr
    (fun k => (conductorCompletedL_divisorIndex_re_mem_Ioo χ hprim hχ k).2.le)
    (conductorCompletedL_zero_sum_absolutely_summable χ hprim hχ hs).of_abs _ hi hj
  rw [← real_logDeriv_conductorCompletedL_eq_divisor_tsum_source χ hprim hχ hquad hs]
  simpa only [add_sub_cancel_left] using hupper q hq χ hχ (1 + 4 * r) hs hs2

theorem analyticOrderAt_eq_one_of_divisor_indices_unique {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfne : f ≠ 0) {z : ℂ} (hz0 : z ≠ 0)
    (hz : f z = 0)
    (hunique : ∀ i j : divisorZeroIndex₀ f Set.univ,
      divisorZeroIndex₀Val i = z → divisorZeroIndex₀Val j = z → i = j) :
    analyticOrderAt f z = 1 := by
  have htop : analyticOrderAt f z ≠ ⊤ := by
    exact fun h => hfne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hf.analyticAt).mp h)
  have hpos : 0 < analyticOrderNatAt f z := by
    rw [Nat.pos_iff_ne_zero, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
    exact ⟨(hf.analyticAt z).analyticOrderAt_ne_zero.mpr hz, htop⟩
  have hnat : analyticOrderNatAt f z = 1 := by
    by_contra hn
    have htwo : 1 < analyticOrderNatAt f z := by omega
    let i : divisorZeroIndex₀ f Set.univ := ⟨⟨z, ⟨0, by
      rw [RealCharacterAnalysis.toNat_divisor_eq_analyticOrderNatAt hf]
      exact hpos⟩⟩, hz0⟩
    let j : divisorZeroIndex₀ f Set.univ := ⟨⟨z, ⟨1, by
      rw [RealCharacterAnalysis.toNat_divisor_eq_analyticOrderNatAt hf]
      exact htwo⟩⟩, hz0⟩
    have heq := hunique i j rfl rfl
    have : (0 : ℕ) = 1 := congrArg (fun p => p.val.snd.val) heq
    omega
  rw [← Nat.cast_analyticOrderNatAt htop, hnat]
  rfl

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.Erdos970.Complex DirichletCharacter _root_.Erdos970.Complex.Hadamard
open scoped ComplexConjugate

theorem exists_classical_near_one_zero_unique_real_simple_jb247_oai :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) (hq : 3 ≤ q),
      let _ : NeZero q := ⟨by omega⟩
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ z : ℂ,
      ‖z - 1‖ ≤ c / Real.log q → LFunction χ z = 0 →
      z.im = 0 ∧ analyticOrderAt (LFunction χ) z = 1 ∧
        ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 → w = z := by
  obtain ⟨c, hc, hc4, hindex_unique⟩ := exists_near_one_divisor_indices_unique
  refine ⟨c, hc, ?_⟩
  intro q hq _ χ hprim hχ hreal z hzdisk hz
  have hquad := (RealCharacterAnalysis.real_values_iff_quadratic χ).mp hreal
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 1 < Real.log q :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hrad : c / Real.log q < 1 / 4 := (div_lt_self hc hlogq).trans hc4
  have hpos : ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → 0 < w.re := by
    intro w hw
    have hre := (Complex.abs_re_le_norm (w - 1)).trans hw
    simp only [Complex.sub_re, Complex.one_re] at hre
    have := (abs_le.mp hre).1
    linarith
  have hf := differentiable_conductorCompletedL χ hχ
  have hfne : conductorCompletedL χ ≠ 0 := by
    intro hzero
    have hzero₁ : conductorCompletedL χ 1 = 0 := congrFun hzero 1
    exact completedL_ne_zero_of_one_le_re χ hχ (s := 1) (by simp)
      ((conductorCompletedL_zero_iff χ 1).mp hzero₁)
  have hzero : ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 →
      conductorCompletedL χ w = 0 := by
    intro w hw hwzero
    rw [conductorCompletedL_zero_iff,
      completedL_eq_mul_gammaFactor χ (hpos w hw), hwzero, zero_mul]
  have hindex : ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 →
      ∃ p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ,
        divisorZeroIndex₀Val p = w := by
    intro w hw hwzero
    apply exists_divisorZeroIndex_val_eq_of_zero hf hfne _ (hzero w hw hwzero)
    intro hw0
    have := hpos w hw
    simp [hw0] at this
  obtain ⟨p, hp⟩ := hindex z hzdisk hz
  have hunique : ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 → w = z := by
    intro w hw hwzero
    obtain ⟨p', hp'⟩ := hindex w hw hwzero
    have heq := hindex_unique q hq χ hprim hχ hquad p' p
      (by simpa only [hp'] using hw) (by simpa only [hp] using hzdisk)
    simpa only [hp', hp] using congrArg divisorZeroIndex₀Val heq
  have hconjzero : LFunction χ (conj z) = 0 := by
    have h := RealCharacterAnalysis.lFunction_conj χ hχ z
    simpa only [hquad.inv, hz, map_zero] using h
  have hconjdisk : ‖conj z - 1‖ ≤ c / Real.log q := by
    have heq : ‖conj z - 1‖ = ‖z - 1‖ := by
      simpa only [map_sub, map_one] using Complex.norm_conj (z - 1)
    rwa [heq]
  have hzim : z.im = 0 := Complex.conj_eq_iff_im.mp (hunique _ hconjdisk hconjzero)
  have horder : analyticOrderAt (conductorCompletedL χ) z = 1 := by
    refine analyticOrderAt_eq_one_of_divisor_indices_unique hf hfne ?_ (hzero z hzdisk hz) ?_
    · intro hz0
      have := hpos z hzdisk
      simp [hz0] at this
    · intro i j hi hj
      exact hindex_unique q hq χ hprim hχ hquad i j
        (by simpa only [hi] using hzdisk) (by simpa only [hj] using hzdisk)
  refine ⟨hzim, ?_, hunique⟩
  rwa [conductorCompletedL_analyticOrderAt_eq_LFunction χ hχ (hpos z hzdisk)] at horder

end WeightedTorusJets

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple_jb247_oai := @OAI.Erdos970.WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple_jb247_oai
