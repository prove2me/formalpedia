-- Prove2me | solution 1 for OAI.Erdos970.ErdosSourceReferenceMargin.root_source_remainder_tendsto_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:06:22.132972+00:00
-- url     : https://prove2.me/submissions/2f06d86c-aedf-4e54-8912-f4cea09ce5ac

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J010
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_HighResidualSum_high_residual_sum_bound_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_LowStateResidualBound_low_state_normalized_residual_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_HighPrimeRemoval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosPrimeInputs.PrimePrefixTail

open _root_.Finset
open PrimePrefixMass

lemma prefixWeight_nonneg (l : List ℕ) : 0 ≤ prefixWeight l := by
  unfold prefixWeight
  apply List.prod_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  positivity

lemma sum_sorted_products (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ l ∈ decreasingPrefixes s, (l.map f).prod) = ∏ p ∈ s, (1 + f p) := by
  rw [decreasingPrefixes, Finset.sum_image]
  · have hp (t : Finset ℕ) : ((t.sort (· ≥ ·)).map f).prod = ∏ p ∈ t, f p := by
      simpa only [Finset.sort_toFinset] using (List.prod_toFinset f (t.sort_nodup (· ≥ ·))).symm
    simp_rw [hp]
    exact (Finset.prod_one_add s).symm
  · intro t ht u hu h
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset h

end ErdosPrimeInputs.PrimePrefixTail



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LinearSieveFunctions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LinearSieveFunctions

open MeasureTheory Filter
open scoped Topology

theorem startingExtension_eq_f (A : ℝ) {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    startingExtension A s = f A s := (f_first_formula A hs2 hs4).symm

end NumberTheoryLean.LinearSieveFunctions

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open DerivativeWeights TransitionKernels

theorem nextGap_div_ratio {r t : ℝ} (ht : 0 < t) : nextGap r t / t = nextExponent r t := by
  unfold nextGap nextExponent
  field_simp

theorem valid_final {i : Side} {s : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) : Valid (finalSide i ts) (finalRatio s ts) := by
  induction ts generalizing i s with
  | nil => exact hs
  | cons t ts ih => exact ih (valid_next hs ht.1) ht.2

theorem nextGap_eq_cost {r t : ℝ} (ht : 0 < t) : nextGap r t = r * Real.exp (-cost t) := by
  have hx : 0 < 1 + 1 / t := by positivity
  unfold cost nextGap
  rw [Real.exp_neg, Real.exp_log hx]
  field_simp

theorem finalGap_eq_cost {i : Side} {s r : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) :
    finalGap r ts = r * Real.exp (-pathCost ts) := by
  induction ts generalizing i s r with
  | nil => simp [finalGap, pathCost]
  | cons t ts ih =>
    have hv := valid_next hs ht.1
    rw [finalGap, ih hv ht.2, nextGap_eq_cost (valid_pos hv), pathCost,
      neg_add, Real.exp_add]
    ring

end NumberTheoryLean.FinitePathGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRatioBins
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeTiltGeometry

open _root_.Erdos970.Set
open FinitePathGeometry ErdosPrimeInputs.HarmonicPrimeMeasure

theorem prime_tilt_step_identity {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s) (hp : p ∈ children w ell S i s r cap closed) :
    (p : ℝ)⁻¹ = primeTilt w r i s p * ((r - primeExponent w p)/r)^2 *
      (weight i s / weight i.flip (childRatio w r p)) := by
  have ht := valid_pos (child_valid hs hp)
  have hw := weight_pos hs
  have hw' := weight_pos (child_valid hs hp)
  rw [← nextGap_childRatio hr (child_exponent_positive hell hp) ht]
  unfold primeTilt nextGap
  field_simp [hr.ne', ht.ne', hw.ne', hw'.ne']

end NumberTheoryLean.PrimeTiltGeometry

end

section

namespace NumberTheoryLean.PrimeTiltPrefixes

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry ErdosPrimeInputs.HarmonicPrimeMeasure
open ErdosPrimeInputs.PrimePrefixMass

theorem ratios_admissible {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) : Admissible i s (primeRatios w r ps) := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => trivial
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    exact ⟨(Finset.mem_filter.mp hp).2.2.2.1, ih hps⟩

theorem primeFinalGap_eq {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    primeFinalGap w r ps = finalGap r (primeRatios w r ps) := by
  induction ps generalizing i s r cap closed with
  | nil => rfl
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    simp only [primeFinalGap, primeRatios, finalGap]
    rw [nextGap_childRatio hr (child_exponent_positive hell hp) (valid_pos (child_valid hs hp))]
    exact ih (child_gap_positive hell hr hs hp) (child_valid hs hp) hps

theorem prime_prefix_weight_identity {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    prefixWeight ps = tiltProduct w i s r ps * (primeFinalGap w r ps / r)^2 *
      (weight i s / weight (finalSide i (primeRatios w r ps)) (finalRatio s (primeRatios w r ps))) := by
  induction ps generalizing i s r cap closed with
  | nil =>
    simp only [prefixWeight, List.map_nil, List.prod_nil, tiltProduct, primeFinalGap, primeRatios, finalSide, finalRatio]
    rw [div_self hr.ne', div_self (weight_pos hs).ne']
    norm_num
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    have hr' := child_gap_positive hell hr hs hp
    have hs' := child_valid hs hp
    have hi := ih hr' hs' hps
    have hf := weight_pos (valid_final hs' (ratios_admissible hps))
    have hstep := prime_tilt_step_identity hell hr hs hp
    simp only [prefixWeight, List.map_cons, List.prod_cons] at ⊢
    change (p : ℝ)⁻¹ * prefixWeight ps = _
    rw [hi, hstep]
    simp only [tiltProduct, primeFinalGap, primeRatios, finalSide, finalRatio]
    field_simp [hr.ne', hr'.ne', (weight_pos hs').ne', hf.ne']

theorem normalized_product_correction {e : ℝ} (he : 0 ≤ e) (w : ℝ) (i : Side) (s r : ℝ) (ps : List ℕ) :
    normalizedTiltProduct e w i s r ps * (1+e)^ps.length = tiltProduct w i s r ps := by
  induction ps generalizing i s r with
  | nil => simp [normalizedTiltProduct, tiltProduct]
  | cons p ps ih =>
    simp only [normalizedTiltProduct, tiltProduct, List.length_cons, pow_succ]
    rw [show (primeTilt w r i s p / (1+e)) * normalizedTiltProduct e w i.flip (childRatio w r p) (r-primeExponent w p) ps *
      ((1+e)^ps.length * (1+e)) = primeTilt w r i s p *
        (normalizedTiltProduct e w i.flip (childRatio w r p) (r-primeExponent w p) ps * (1+e)^ps.length) by
          field_simp [show 1+e ≠ 0 by linarith]]
    rw [ih]

theorem normalized_prime_prefix_weight_identity {w ell S s r cap e : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (he : 0 ≤ e) (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    prefixWeight ps = normalizedTiltProduct e w i s r ps * (1+e)^ps.length * (primeFinalGap w r ps / r)^2 *
      (weight i s / weight (finalSide i (primeRatios w r ps)) (finalRatio s (primeRatios w r ps))) := by
  rw [normalized_product_correction he]
  exact prime_prefix_weight_identity hell hr hs hpath

end NumberTheoryLean.PrimeTiltPrefixes

end

section

namespace NumberTheoryLean.PrimeHistories

open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_gap_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).gap = primeFinalGap w z.gap ps := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeFinalGap, step] using ih (step w z p)

theorem terminal_ratio_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).ratio = finalRatio z.ratio (primeRatios w z.gap ps) := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeRatios, finalRatio, step] using ih (step w z p)

theorem terminal_side_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).side = finalSide z.side (primeRatios w z.gap ps) := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeRatios, finalSide, step] using ih (step w z p)

end NumberTheoryLean.PrimeHistories

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceWeightedQuadrature
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.ReferenceDifferentiation

open _root_.Filter _root_.Set
open scoped Topology
open FinitePathGeometry LinearSieveFunctions BuchstabBridge ReferenceBenchmarkDecay

theorem parent_even_eq_ordinary {s : ℝ} (hs : 2 ≤ s) :
    parentBenchmark .even s = benchmark .even s := by
  simp only [parentBenchmark,benchmark]
  split_ifs with h
  · exact startingExtension_eq_f sieveA hs (by linarith)
  · rfl

theorem omitted_lower_deviation {r x : ℝ} (hx : 0 < x) (homit : r-x < 2*x) :
    benchmark .even (r/x-1)-1 = -1 := by
  have hs : r/x-1 ≤ 2 := by
    have hd : r/x < 3 := (div_lt_iff₀ hx).mpr (by linarith)
    linarith
  rw [benchmark_even_below_two hs]
  ring

end NumberTheoryLean.ReferenceDifferentiation



namespace NumberTheoryLean.ReferenceAdmission

open _root_.Finset
open FinitePathGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

theorem boundary_prime_exponent_upper {w : ℝ} (hw : 1 < w) {p : ℕ} (hp : p ∈ boundaryPrimes w) :
    primeExponent w p ≤ 2 := by
  obtain ⟨hpp,_⟩ := Finset.mem_filter.mp hp
  obtain ⟨hfloor,hprime⟩ := Nat.mem_primesLE.mp hpp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  apply (exponent_le_iff hw hp0).mpr
  exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) 2).le).mp hfloor

end NumberTheoryLean.ReferenceAdmission


namespace NumberTheoryLean.ReferenceCancellation

open _root_.MeasureTheory _root_.Set
open FinitePathGeometry LinearSieveFunctions BuchstabBridge ReferenceBenchmarkDecay
open ReferenceDifferentiation ReferenceAdmission

theorem upper_admission_above_two {r x : ℝ} (hx : 2 ≤ x) :
    childAdmitted .odd r x ↔ 2*x ≤ r-x := by
  change max (2*x) (x+2) ≤ r-x ↔ 2*x ≤ r-x
  rw [max_eq_left (by linarith)]

theorem actual_omitted_deviation_above_two {r x : ℝ} (hx : 2 ≤ x)
    (homit : ¬childAdmitted .odd r x) :
    benchmark .even (r/x-1)-1 = -1 := by
  rw [upper_admission_above_two hx] at homit
  exact omitted_lower_deviation (by linarith) (lt_of_not_ge homit)

end NumberTheoryLean.ReferenceCancellation



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_BoundaryPrimeMass
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.VariablePrimeTilt

open _root_.Finset
open ReferenceAdmission FinitePathGeometry
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem variable_tilt_weight (t : ℝ) (ps : List ℕ) :
    (ps.map (fun p : ℕ => t*(p:ℝ)⁻¹)).prod=t^ps.length*prefixWeight ps := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,prefixWeight] at ih ⊢
    rw [ih]
    ring

end NumberTheoryLean.VariablePrimeTilt

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PrefixCompletions
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePruning
attribute [local instance] Classical.propDecidable
open ErdosPrimeInputs.PrimePrefixMass

theorem append_mem_decreasing_iff {P : Finset ℕ} {pre suf : List ℕ}
    (hpre : pre ∈ decreasingPrefixes P) :
    pre++suf ∈ decreasingPrefixes P ↔ suf ∈ decreasingPrefixes (suffixPrimes P pre) := by
  obtain ⟨hpp,hpm⟩ := mem_decreasingPrefixes.mp hpre
  constructor
  · intro h
    obtain ⟨hp,hm⟩ := mem_decreasingPrefixes.mp h
    obtain ⟨_,hs,hcross⟩ := List.pairwise_append.mp hp
    apply mem_decreasingPrefixes.mpr
    refine ⟨hs,?_⟩
    intro q hq
    apply Finset.mem_filter.mpr
    exact ⟨hm q (List.mem_append.mpr (Or.inr hq)),fun p hp => hcross p hp q hq⟩
  · intro h
    obtain ⟨hs,hm⟩ := mem_decreasingPrefixes.mp h
    apply mem_decreasingPrefixes.mpr
    refine ⟨List.pairwise_append.mpr ⟨hpp,hs,?_⟩,?_⟩
    · intro p hp q hq
      exact (Finset.mem_filter.mp (hm q hq)).2 p hp
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hpm p hp
      · exact (Finset.mem_filter.mp (hm p hp)).1

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceProductsBasics
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open scoped BigOperators
namespace NumberTheoryLean.ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem sum_signedWeight (P : Finset ℕ) :
    (∑ ps ∈ decreasingPrefixes P,signedWeight ps) = survivorProduct P := by
  have h := sum_sorted_products P (fun p : ℕ => (-1 : ℝ)*(p : ℝ)⁻¹)
  simp_rw [VariablePrimeTilt.variable_tilt_weight] at h
  simpa only [signedWeight,survivorProduct,neg_one_mul,sub_eq_add_neg] using h

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ReferencePrefixRecurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePrefixRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem singleton_prefix_mem {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) : [p] ∈ decreasingPrefixes P := by
  apply mem_decreasingPrefixes.mpr
  exact ⟨by simp,by intro q hq; simpa using List.mem_singleton.mp hq ▸ hp⟩

theorem nonempty_eq_first_completions (P : Finset ℕ) :
    nonemptyPrefixes P=P.biUnion (fun p => completions P [p]) := by
  ext ps
  constructor
  · intro hp
    obtain ⟨hpD,hne⟩ := Finset.mem_filter.mp hp
    cases ps with
    | nil => exact False.elim (hne rfl)
    | cons p ps =>
      have hpP : p ∈ P := (mem_decreasingPrefixes.mp hpD).2 p (by simp)
      have ht := (append_mem_decreasing_iff (singleton_prefix_mem hpP)).mp hpD
      exact Finset.mem_biUnion.mpr ⟨p,hpP,Finset.mem_image.mpr ⟨ps,ht,rfl⟩⟩
  · intro hp
    obtain ⟨p,hpP,hps⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨tail,htail,rfl⟩ := Finset.mem_image.mp hps
    exact Finset.mem_filter.mpr ⟨(append_mem_decreasing_iff (singleton_prefix_mem hpP)).mpr htail,by simp⟩

theorem first_completions_disjoint (P : Finset ℕ) :
    (P:Set ℕ).PairwiseDisjoint (fun p => completions P [p]) := by
  intro p _hp q _hq hne
  apply Finset.disjoint_left.mpr
  intro ps hp hq
  obtain ⟨sp,_hsp,he⟩ := Finset.mem_image.mp hp
  obtain ⟨sq,_hsq,hf⟩ := Finset.mem_image.mp hq
  have hh := he.trans hf.symm
  simp only [List.singleton_append] at hh
  exact hne (List.cons.inj hh).1

theorem sum_decreasing_by_first (P : Finset ℕ) (F : List ℕ → ℝ) :
    (∑ ps ∈ decreasingPrefixes P,F ps)=F []+
      ∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),F (p::ps) := by
  have he : (decreasingPrefixes P).filter (fun ps => ps=[])= {[]} := by
    ext ps
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h
      subst ps
      exact ⟨mem_decreasingPrefixes.mpr ⟨by simp,by simp⟩,rfl⟩
  have hs := Finset.sum_filter_add_sum_filter_not (decreasingPrefixes P) (fun ps => ps=[]) F
  rw [he,Finset.sum_singleton] at hs
  change F []+(∑ ps ∈ nonemptyPrefixes P,F ps)=(∑ ps ∈ decreasingPrefixes P,F ps) at hs
  rw [← hs,nonempty_eq_first_completions,Finset.sum_biUnion (first_completions_disjoint P)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  unfold completions
  rw [Finset.sum_image]
  · have hsuf : suffixPrimes P [p]=P.filter (fun q => q<p) := by simp [suffixPrimes]
    rw [hsuf]
    apply Finset.sum_congr rfl
    intro ps _
    rfl
  · intro a _ b _ h
    exact List.append_cancel_left h

theorem reference_polynomial_recurrence (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    referencePolynomial w P i r=1-
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0 := by
  have h := sum_decreasing_by_first P (fun ps => if admitted w i r ps then signedWeight ps else 0)
  have he : referencePolynomial w P i r =
      ∑ ps ∈ decreasingPrefixes P,if admitted w i r ps then signedWeight ps else 0 := by
    rw [referencePolynomial,referencePrefixes,Finset.sum_filter]
    rfl
  have hnil : (if admitted w i r [] then signedWeight [] else 0)=1 := by
    simp [admitted,signedWeight,prefixWeight]
  rw [he,h,hnil]
  have hsum : (∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),
      if admitted w i r (p::ps) then signedWeight (p::ps) else 0) =
      -(∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hc : childAdmitted i r (primeExponent w p)
    · rw [ite_eq_left hc,referencePolynomial,referencePrefixes,Finset.sum_filter]
      rw [Finset.mul_sum,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ps _
      simp only [admitted,hc,true_and,signedWeight,List.length_cons,pow_succ,
        prefixWeight,List.map_cons,List.prod_cons]
      split_ifs <;> ring
    · simp [admitted,hc]
  rw [hsum]
  ring

end NumberTheoryLean.ReferencePrefixRecurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceCutoffRecurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_none _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceWeightedRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning ReferencePrefixRecurrence
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem weighted_reference_recurrence (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (F : List ℕ → ℝ) :
    weightedValue w P i r F=F []-
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*weightedValue w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) (fun ps => F (p::ps)) else 0 := by
  have h := sum_decreasing_by_first P (fun ps => if admitted w i r ps then signedWeight ps*F ps else 0)
  have he : weightedValue w P i r F =
      ∑ ps ∈ decreasingPrefixes P,if admitted w i r ps then signedWeight ps*F ps else 0 := by
    rw [weightedValue,referencePrefixes,Finset.sum_filter]
  have hnil : (if admitted w i r [] then signedWeight []*F [] else 0)=F [] := by
    simp [admitted,signedWeight,prefixWeight]
  rw [he,h,hnil]
  have hsum : (∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),
      if admitted w i r (p::ps) then signedWeight (p::ps)*F (p::ps) else 0) =
      -(∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*weightedValue w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) (fun ps => F (p::ps)) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hc : childAdmitted i r (primeExponent w p)
    · rw [ite_eq_left hc,weightedValue,referencePrefixes,Finset.sum_filter]
      rw [Finset.mul_sum,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ps _
      simp only [admitted,hc,true_and,signedWeight,List.length_cons,pow_succ,
        prefixWeight,List.map_cons,List.prod_cons]
      split_ifs <;> ring
    · simp [admitted,hc]
  rw [hsum]
  ring

end NumberTheoryLean.ReferenceWeightedRecurrence

end

section

namespace NumberTheoryLean.ReferenceForestTelescoping

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePruning ReferenceWeightedRecurrence
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem suffixPrimes_nil (P : Finset ℕ) : suffixPrimes P []=P := by simp [suffixPrimes]

theorem suffixPrimes_cons (P : Finset ℕ) (p : ℕ) (ps : List ℕ) :
    suffixPrimes P (p::ps)=suffixPrimes (P.filter (fun q => q<p)) ps := by
  ext q
  simp [suffixPrimes,and_assoc,and_left_comm,and_comm]

theorem forestSum_recurrence (w : ℝ) (P : Finset ℕ) (z : Node) (G : Finset ℕ → Node → ℝ) :
    forestSum w P z G=G P z-
      ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
        (p:ℝ)⁻¹*forestSum w (P.filter (fun q => q<p)) (step w z p) G else 0 := by
  have h := weighted_reference_recurrence w P z.side z.gap (fun ps => G (suffixPrimes P ps) (terminal w z ps))
  simpa only [forestSum,suffixPrimes_nil,terminal_nil,suffixPrimes_cons,terminal_cons,step] using h

theorem actual_forest_telescoping (w : ℝ) (G : Finset ℕ → Node → ℝ) (P : Finset ℕ) (z : Node) :
    forestSum w P z (recurrenceResidual w G)=G P z := by
  revert z
  refine Finset.strongInductionOn P ?_
  intro P ih z
  rw [forestSum_recurrence]
  have hs : (∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*forestSum w (P.filter (fun q => q<p)) (step w z p) (recurrenceResidual w G) else 0)=
      ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
        (p:ℝ)⁻¹*G (P.filter (fun q => q<p)) (step w z p) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hsmall : P.filter (fun q => q<p) ⊂ P :=
      Finset.filter_ssubset.mpr ⟨p,hp,lt_irrefl p⟩
    rw [ih _ hsmall]
  rw [hs,recurrenceResidual]
  ring

end NumberTheoryLean.ReferenceForestTelescoping

end

section

namespace NumberTheoryLean.ReferenceCutoffRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories ReferenceAdmission ReferencePruning
open ReferencePrefixRecurrence ReferenceWeightedRecurrence ReferenceForestTelescoping
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem above_disjoint {P Q : Finset ℕ} (h : Above P Q) : Disjoint P Q := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact lt_irrefl p (h p hp p hq)

theorem union_filter_at_high {P Q : Finset ℕ} (h : Above P Q) {p : ℕ} (hp : p ∈ P) :
    (P∪Q).filter (fun q => q<p)=(P.filter (fun q => q<p))∪Q := by
  rw [Finset.filter_union,Finset.filter_eq_self.mpr (h p hp)]

theorem union_filter_at_low {P Q : Finset ℕ} (h : Above P Q) {p : ℕ} (hp : p ∈ Q) :
    (P∪Q).filter (fun q => q<p)=Q.filter (fun q => q<p) := by
  ext q
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hq,hqp⟩
    rcases hq with hq | hq
    · exact False.elim (lt_asymm hqp (h q hq p hp))
    · exact ⟨hq,hqp⟩
  · rintro ⟨hq,hqp⟩
    exact ⟨Or.inr hq,hqp⟩

theorem cutoff_polynomial_recurrence (w : ℝ) {P Q : Finset ℕ} (h : Above P Q) (i : Side) (r : ℝ) :
    referencePolynomial w (P∪Q) i r=referencePolynomial w Q i r-
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P.filter (fun q => q<p))∪Q) i.flip (r-primeExponent w p) else 0 := by
  have hfull := reference_polynomial_recurrence w (P∪Q) i r
  have hlow := reference_polynomial_recurrence w Q i r
  rw [Finset.sum_union (above_disjoint h)] at hfull
  have hh : (∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P∪Q).filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0)=
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P.filter (fun q => q<p))∪Q) i.flip (r-primeExponent w p) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_high h hp]
  have hl : (∑ p ∈ Q,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w ((P∪Q).filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0)=
      ∑ p ∈ Q,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (Q.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_low h hp]
  rw [hh,hl] at hfull
  linarith

theorem difference_residual (w : ℝ) {P Q : Finset ℕ} (h : Above P Q)
    (B : Finset ℕ → Node → ℝ) (z : Node) :
    recurrenceResidual w (fun S y => referencePolynomial w (S∪Q) y.side y.gap-B S y) P z=
      cutoffInsertion w Q B P z := by
  have hrec := cutoff_polynomial_recurrence w h z.side z.gap
  have hsum : (∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*(referencePolynomial w ((P.filter (fun q => q<p))∪Q) (step w z p).side (step w z p).gap-
        B (P.filter (fun q => q<p)) (step w z p)) else 0)=
    (∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*referencePolynomial w ((P.filter (fun q => q<p))∪Q) z.side.flip (z.gap-primeExponent w p) else 0)-
    ∑ p ∈ P,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*B (P.filter (fun q => q<p)) (step w z p) else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    split_ifs <;> simp [step,mul_sub]
  unfold recurrenceResidual cutoffInsertion
  dsimp only
  rw [hsum]
  linarith

theorem finite_cutoff_decomposition (w : ℝ) {P Q : Finset ℕ} (h : Above P Q)
    (B : Finset ℕ → Node → ℝ) (z : Node) :
    referencePolynomial w (P∪Q) z.side z.gap-B P z=
      forestSum w P z (cutoffInsertion w Q B) := by
  let G : Finset ℕ → Node → ℝ := fun S y => referencePolynomial w (S∪Q) y.side y.gap-B S y
  have ht := actual_forest_telescoping w G P z
  change G P z=_
  rw [← ht]
  unfold forestSum weightedValue
  apply Finset.sum_congr rfl
  intro ps _hp
  have hsub : Above (suffixPrimes P ps) Q := by
    intro p hp q hq
    exact h p (Finset.mem_filter.mp hp).1 q hq
  dsimp only
  rw [show recurrenceResidual w G (suffixPrimes P ps) (terminal w z ps)=
      cutoffInsertion w Q B (suffixPrimes P ps) (terminal w z ps) from difference_residual w hsub B _]

end NumberTheoryLean.ReferenceCutoffRecurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ReferenceSourcePrimeSets
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceSourcePrimeSets

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeTiltGeometry ReferenceAdmission ReferencePruning ReferenceProductsBasics
open ReferenceMertens ReferenceCutoffRecurrence
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

theorem availablePrimes_membership {a x : ℝ} (hx : 0 ≤ x) (closed : Bool) (p : ℕ) :
    p ∈ availablePrimes a x closed ↔ p.Prime ∧ a<(p:ℝ) ∧ (if closed then (p:ℝ) ≤ x else (p:ℝ)<x) := by
  simp only [availablePrimes,primesBetween,Finset.mem_filter,Nat.mem_primesLE,Nat.le_floor_iff hx]
  cases closed
  · simp only [Bool.false_eq_true,false_or,ite_false, if_false]
    constructor
    · rintro ⟨⟨⟨_,hp⟩,ha⟩,hx⟩
      exact ⟨hp,ha,hx⟩
    · rintro ⟨hp,ha,hx⟩
      exact ⟨⟨⟨hx.le,hp⟩,ha⟩,hx⟩
  · simp only [true_or,ite_true, if_true,and_true]
    tauto

theorem sourcePrimes_membership {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) (p : ℕ) :
    p ∈ sourcePrimes w b closed ↔ p.Prime ∧ 1<primeExponent w p ∧ capGuard closed b (primeExponent w p) := by
  rw [sourcePrimes,availablePrimes_membership (Real.rpow_pos_of_pos (by linarith : 0 < w) b).le]
  constructor
  · rintro ⟨hp,hlo,hhi⟩
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
    refine ⟨hp,?_,?_⟩
    · exact (lt_exponent_iff hw hp0).mpr (by simpa only [Real.rpow_one] using hlo)
    · cases closed with
      | false => exact (exponent_lt_iff hw hp0).mpr hhi
      | true => exact (exponent_le_iff hw hp0).mpr hhi
  · rintro ⟨hp,hlo,hhi⟩
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
    refine ⟨hp,?_,?_⟩
    · simpa only [Real.rpow_one] using (lt_exponent_iff hw hp0).mp hlo
    · cases closed with
      | false => exact (exponent_lt_iff hw hp0).mp hhi
      | true => exact (exponent_le_iff hw hp0).mp hhi

theorem highPrimes_membership {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) (p : ℕ) :
    p ∈ highPrimes w b closed ↔ p.Prime ∧ 2<primeExponent w p ∧ capGuard closed b (primeExponent w p) := by
  rw [highPrimes,Finset.mem_filter,sourcePrimes_membership hw]
  constructor
  · rintro ⟨⟨hp,_hlo,hcap⟩,hhi⟩
    exact ⟨hp,(lt_exponent_iff hw (by exact_mod_cast hp.pos)).mpr hhi,hcap⟩
  · rintro ⟨hp,hhi,hcap⟩
    exact ⟨⟨hp,by linarith,hcap⟩,(lt_exponent_iff hw (by exact_mod_cast hp.pos)).mp hhi⟩

theorem boundary_subset_source {w b : ℝ} (hw : 1 < w) (hb : 2 < b) (closed : Bool) :
    boundaryPrimes w ⊆ sourcePrimes w b closed := by
  intro p hp
  have hpl := (sourcePrimes_membership hw 2 true p).mp (by rwa [sourcePrimes_boundary])
  apply (sourcePrimes_membership hw b closed p).mpr
  refine ⟨hpl.1,hpl.2.1,?_⟩
  have hle : primeExponent w p ≤ 2 := hpl.2.2
  cases closed with
  | false => exact hle.trans_lt hb
  | true => exact hle.trans hb.le

theorem sourcePrimes_partition {w b : ℝ} (hw : 1 < w) (hb : 2 < b) (closed : Bool) :
    sourcePrimes w b closed=highPrimes w b closed ∪ boundaryPrimes w := by
  ext p
  constructor
  · intro hp
    by_cases hhi : w^(2:ℝ)<(p:ℝ)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp,hhi⟩))
    · have hpm := (sourcePrimes_membership hw b closed p).mp hp
      apply Finset.mem_union.mpr
      right
      rw [← sourcePrimes_boundary]
      apply (sourcePrimes_membership hw 2 true p).mpr
      refine ⟨hpm.1,hpm.2.1,?_⟩
      exact (exponent_le_iff hw (by exact_mod_cast hpm.1.pos)).mpr (le_of_not_gt hhi)
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).1
    · exact boundary_subset_source hw hb closed hp

theorem highPrimes_above_boundary {w b : ℝ} (hw : 1 < w) (closed : Bool) :
    Above (highPrimes w b closed) (boundaryPrimes w) := by
  intro p hp q hq
  have hpHi := (Finset.mem_filter.mp hp).2
  have hqB := boundary_prime_exponent_upper hw hq
  have hqP : q.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
  have hqLe := (exponent_le_iff hw (by exact_mod_cast hqP.pos)).mp hqB
  exact_mod_cast hqLe.trans_lt hpHi

theorem rpow_primeExponent {w : ℝ} (hw : 1 < w) {p : ℕ} (hp : p.Prime) :
    w^primeExponent w p=(p:ℝ) := by
  have hw0 : 0 < w := by linarith
  rw [Real.rpow_def_of_pos hw0]
  have he : Real.log w*primeExponent w p=Real.log p := by
    unfold primeExponent
    field_simp [ne_of_gt (Real.log_pos hw)]
  rw [he,Real.exp_log (by exact_mod_cast hp.pos)]

theorem sourcePrimes_at_selected {w b : ℝ} (hw : 1 < w) (closed : Bool) {p : ℕ}
    (hp : p ∈ sourcePrimes w b closed) :
    sourcePrimes w (primeExponent w p) false=(sourcePrimes w b closed).filter (fun q => q<p) := by
  have hpM := (sourcePrimes_membership hw b closed p).mp hp
  have hpCap : primeExponent w p ≤ b := by
    cases closed with
    | false => exact hpM.2.2.le
    | true => exact hpM.2.2
  ext q
  rw [sourcePrimes_membership hw,Finset.mem_filter,sourcePrimes_membership hw]
  constructor
  · rintro ⟨hq,hqLo,hqCap⟩
    have hqCap' : primeExponent w q < primeExponent w p := hqCap
    have hqP : q<p := by
      have hreal := (exponent_lt_iff hw (by exact_mod_cast hq.pos)).mp hqCap'
      rw [rpow_primeExponent hw hpM.1] at hreal
      exact_mod_cast hreal
    refine ⟨⟨hq,hqLo,?_⟩,hqP⟩
    cases closed with
    | false => exact hqCap'.trans_le hpCap
    | true => exact hqCap'.le.trans hpCap
  · rintro ⟨⟨hq,hqLo,_hqCap⟩,hqp⟩
    refine ⟨hq,hqLo,?_⟩
    apply (exponent_lt_iff hw (by exact_mod_cast hq.pos)).mpr
    rw [rpow_primeExponent hw hpM.1]
    exact_mod_cast hqp

end NumberTheoryLean.ReferenceSourcePrimeSets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ReferenceEulerRecurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceEulerRecurrence

open _root_.Finset
open ReferencePruning ReferencePrefixRecurrence ReferenceCutoffRecurrence
open ReferenceSourcePrimeSets ReferenceProductsBasics ReferenceMertens ReferenceAdmission
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

lemma signedWeight_cons (p : ℕ) (ps : List ℕ) :
    signedWeight (p::ps)=(-(p:ℝ)⁻¹)*signedWeight ps := by
  simp only [signedWeight,List.length_cons,pow_succ,prefixWeight,List.map_cons,List.prod_cons]
  ring

theorem survivor_first_recurrence (P : Finset ℕ) :
    survivorProduct P=1-∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct (P.filter (fun q => q<p)) := by
  have h := sum_decreasing_by_first P signedWeight
  rw [sum_signedWeight] at h
  have hnil : signedWeight []=1 := by simp [signedWeight,prefixWeight]
  rw [hnil] at h
  have hs : (∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),signedWeight (p::ps))=
      -(∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct (P.filter (fun q => q<p))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    simp_rw [signedWeight_cons]
    rw [← Finset.mul_sum,sum_signedWeight]
    ring
  rw [hs] at h
  linarith

theorem survivor_cutoff_recurrence {P Q : Finset ℕ} (h : Above P Q) :
    survivorProduct (P∪Q)=survivorProduct Q-
      ∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct ((P.filter (fun q => q<p))∪Q) := by
  have hf := survivor_first_recurrence (P∪Q)
  have hl := survivor_first_recurrence Q
  rw [Finset.sum_union (above_disjoint h)] at hf
  have hhi : (∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct ((P∪Q).filter (fun q => q<p)))=
      ∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct ((P.filter (fun q => q<p))∪Q) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_high h hp]
  have hlo : (∑ p ∈ Q,(p:ℝ)⁻¹*survivorProduct ((P∪Q).filter (fun q => q<p)))=
      ∑ p ∈ Q,(p:ℝ)⁻¹*survivorProduct (Q.filter (fun q => q<p)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_low h hp]
  rw [hhi,hlo] at hf
  linarith

theorem referenceProduct_eq_survivor (w b : ℝ) (closed : Bool) :
    referenceProduct w b closed=survivorProduct (sourcePrimes w b closed) := rfl

theorem highPrimes_at_selected {w b : ℝ} (hw : 1 < w) (closed : Bool) {p : ℕ}
    (hp : p ∈ sourcePrimes w b closed) :
    highPrimes w (primeExponent w p) false=(highPrimes w b closed).filter (fun q => q<p) := by
  ext q
  simp only [highPrimes,Finset.mem_filter,sourcePrimes_at_selected hw closed hp]
  tauto

theorem actual_product_cutoff_identity {w b : ℝ} (hw : 1 < w) (hb : 2 < b) (closed : Bool) :
    referenceProduct w b closed=referenceProduct w 2 true-
      ∑ p ∈ highPrimes w b closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false := by
  have hsep := highPrimes_above_boundary (b:=b) hw closed
  have hr := survivor_cutoff_recurrence hsep
  have hpart := sourcePrimes_partition hw hb closed
  rw [← hpart] at hr
  have hbase : survivorProduct (boundaryPrimes w)=referenceProduct w 2 true := by
    rw [referenceProduct_eq_survivor,sourcePrimes_boundary]
  rw [hbase] at hr
  change referenceProduct w b closed=referenceProduct w 2 true-
    (∑ p ∈ highPrimes w b closed,(p:ℝ)⁻¹*survivorProduct (((highPrimes w b closed).filter (fun q => q<p))∪boundaryPrimes w)) at hr
  rw [hr]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpS : p ∈ sourcePrimes w b closed := (Finset.mem_filter.mp hp).1
  have hchild := sourcePrimes_at_selected hw closed hpS
  rw [hpart,union_filter_at_high hsep hp] at hchild
  rw [referenceProduct_eq_survivor,hchild]

end NumberTheoryLean.ReferenceEulerRecurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceLocalResidual
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceLocalResidual

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeTiltGeometry ReferenceAdmission ReferencePruning
open ReferenceSourcePrimeSets ReferenceEulerRecurrence ReferenceMertens ReferenceDifferentiation
open ReferenceBenchmarkDecay ReferenceCancellation BoundaryAnomaly
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem admitted_child_benchmark {w : ℝ} (hw : 1 < w) (z : Node) {p : ℕ}
    (hp : p ∈ highPrimes w z.cutoff z.closed) (ha : childAdmitted z.side z.gap (primeExponent w p)) :
    nodeBenchmark w (step w z p)=referenceProduct w (primeExponent w p) false*
      benchmark z.side.flip (childRatio w z.gap p) := by
  have hxp := (highPrimes_membership hw z.cutoff z.closed p).mp hp |>.2.1
  unfold nodeBenchmark
  simp only [step]
  congr 1
  cases hi : z.side with
  | even => rfl
  | odd =>
    have hh : 2*primeExponent w p ≤ z.gap-primeExponent w p := by
      rw [hi] at ha
      exact (upper_admission_above_two hxp.le).mp ha
    have hc : 2 ≤ childRatio w z.gap p := by
      unfold childRatio
      have hd : 3 ≤ z.gap/primeExponent w p := (le_div_iff₀ (by linarith)).mpr (by linarith)
      linarith
    exact parent_even_eq_ordinary hc

theorem omitted_child_benchmark {w : ℝ} (hw : 1 < w) (z : Node) {p : ℕ}
    (hp : p ∈ highPrimes w z.cutoff z.closed) (ha : ¬childAdmitted z.side z.gap (primeExponent w p)) :
    benchmark z.side.flip (childRatio w z.gap p)=0 := by
  have hxp := (highPrimes_membership hw z.cutoff z.closed p).mp hp |>.2.1
  cases hi : z.side with
  | even => exact False.elim (ha (by rw [hi]; trivial))
  | odd =>
    have hh := actual_omitted_deviation_above_two hxp.le (by rwa [hi] at ha)
    change benchmark .even (z.gap/primeExponent w p-1)=0
    linarith

theorem admitted_benchmark_sum {w : ℝ} (hw : 1 < w) (z : Node) :
    (∑ p ∈ highPrimes w z.cutoff z.closed,if childAdmitted z.side z.gap (primeExponent w p) then
      (p:ℝ)⁻¹*nodeBenchmark w (step w z p) else 0)=
    ∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      benchmark z.side.flip (childRatio w z.gap p) := by
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ha : childAdmitted z.side z.gap (primeExponent w p)
  · rw [ite_eq_left ha,admitted_child_benchmark hw z hp ha]
    ring
  · rw [ite_eq_right ha,omitted_child_benchmark hw z hp ha,mul_zero]

theorem source_insertion_identity {w : ℝ} (hw : 1 < w) (z : Node) (hb : 2 < z.cutoff) :
    sourceInsertion w z=anomaly w z.side z.gap+sourceResidual w z := by
  have hp := actual_product_cutoff_identity hw hb z.closed
  have hsum : (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      (benchmark z.side.flip (childRatio w z.gap p)-1))=
    (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      benchmark z.side.flip (childRatio w z.gap p))-
    ∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  have hbase : survivorProduct (boundaryPrimes w)=referenceProduct w 2 true := by
    rw [referenceProduct_eq_survivor,sourcePrimes_boundary]
  unfold sourceInsertion sourceResidual anomaly
  rw [admitted_benchmark_sum hw z,hsum,hbase]
  unfold nodeBenchmark
  linarith

end NumberTheoryLean.ReferenceLocalResidual

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightIntegrals
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoStepDensityBounds

open Set
open DerivativeWeights WeightFutureIntegrals FinitePathGeometry

theorem weight_antitone {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i t) (hst : s ≤ t) :
    weight i t ≤ weight i s := by
  cases i with
  | even =>
    exact phiEven_strictAntiOn.antitoneOn
      (by change 1 < s; dsimp [Valid] at hs <;> linarith)
      (by change 1 < t; dsimp [Valid] at ht <;> linarith) hst
  | odd => exact phiOdd_antitone hst

end NumberTheoryLean.TwoStepDensityBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LowStateHorizon

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open ArrivalKernelGeometry RegeneratingInverseBands HarmonicWeightKernel

 theorem cost_ge_inv_add_one {t : ℝ} (ht : 0 < t) : 1 / (t + 1) ≤ cost t := by
  have hx : 0 < 1 + 1 / t := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have heq : 1 - (1 + 1 / t)⁻¹ = 1 / (t + 1) := by
    field_simp [ht.ne', hx.ne', show t + 1 ≠ 0 by linarith]
    ring
  rw [heq] at h
  exact h

theorem source_horizon_log_cube {B : ℝ} (hB : 2 ≤ Real.log B) :
    ((sourceHorizon ((Real.log B) ^ 2) B : ℕ) : ℝ) ≤ 5 * (Real.log B) ^ 3 := by
  let x := Real.log B
  have hx : 2 ≤ x := hB
  have hpos : 0 ≤ (x ^ 2 + 1) * (x + 2) := by positivity
  have hc := (Nat.ceil_lt_add_one hpos).le
  change ((⌈(x ^ 2 + 1) * (x + 2)⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * x ^ 3
  push_cast
  have h2 : 0 ≤ (x - 2) * x := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (x - 2) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  nlinarith

end NumberTheoryLean.LowStateHorizon

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeGridGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.PrimeKilledChain

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeRowNormalization

 theorem normalizationRate_pos : 0 < normalizationRate :=
  (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).1

theorem normalizationThreshold_gt_one : 1 < normalizationThreshold :=
  (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).2.1

variable (w ell S : ℝ) (start : Node)

variable {w ell S : ℝ} {start : Node}

theorem pathLaw_isProbability (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (n : ℕ) :
    IsProbabilityMeasure (pathLaw w ell S start n) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  unfold pathLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.PrimeKilledChain



namespace NumberTheoryLean.PrimeChainProbabilities

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeKilledChain

variable {w ell S : ℝ} {start : Node}

theorem history_append_eq_iff (h k : History w ell S start) (p q : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) (hq : q ∈ nodeChildren w ell S k.node) :
    h.append p hp = k.append q hq ↔ h = k ∧ p = q := by
  constructor
  · intro heq
    have hl := congrArg History.primes heq
    have hh := List.append_singleton_inj.mp hl
    exact ⟨History.ext hh.1,hh.2⟩
  · rintro ⟨rfl,rfl⟩
    exact History.ext rfl

theorem liveLaw_at_append (g h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) :
    liveLaw w ell S start g {some (h.append p hp)} =
      ({h} : Set (History w ell S start)).indicator (fun _ => childProbability w ell S start h p) g := by
  classical
  simp only [liveLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator, Set.mem_singleton_iff, Pi.one_apply, Option.some.injEq, history_append_eq_iff,
    mul_ite, mul_one, mul_zero]
  by_cases hgh : g = h
  · subst g
    simp only [true_and, ite_true, if_true]
    calc
      _ = ∑ q ∈ nodeChildren w ell S h.node, if q = p then childProbability w ell S start h q else 0 :=
        Finset.sum_attach _ (fun q : ℕ => if q = p then childProbability w ell S start h q else 0)
      _ = _ := by simp [hp]
  · simp [hgh]

theorem chain_at_append (h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) (z : ChainState w ell S start) :
    chain w ell S start z {some (h.append p hp)} =
      ({some h} : Set (ChainState w ell S start)).indicator (fun _ => childProbability w ell S start h p) z := by
  classical
  cases z with
  | none => simp [chain_none, Set.indicator]
  | some g =>
    rw [chain_some, completedLaw, Measure.add_apply, liveLaw_at_append, Measure.smul_apply]
    simp [Set.indicator]

theorem pathLaw_append (n : ℕ) (h : History w ell S start) (p : ℕ)
    (hp : p ∈ nodeChildren w ell S h.node) :
    pathLaw w ell S start (n+1) {some (h.append p hp)} =
      childProbability w ell S start h p * pathLaw w ell S start n {some h} := by
  unfold pathLaw
  have hpow : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
  rw [hpow, Kernel.comp_apply' _ _ _ (measurableSet_singleton _)]
  calc
    _ = ∫⁻ z, ({some h} : Set (ChainState w ell S start)).indicator
        (fun _ => childProbability w ell S start h p) z ∂((chain w ell S start)^n) (some History.empty) :=
      lintegral_congr (fun z => chain_at_append h p hp z)
    _ = _ := by rw [lintegral_indicator (measurableSet_singleton _), lintegral_const, Measure.restrict_apply_univ]

theorem nodeProduct_append (e w : ℝ) (z : Node) (ps qs : List ℕ) :
    nodeProduct e w z (ps++qs) = nodeProduct e w z ps * nodeProduct e w (terminal w z ps) qs := by
  induction ps generalizing z with
  | nil => simp [nodeProduct, normalizedTiltProduct, terminal]
  | cons p ps ih =>
    change (primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) (ps++qs) =
      ((primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) ps) *
        nodeProduct e w (terminal w (step w z p) ps) qs
    rw [ih, mul_assoc]

theorem nodeProduct_nonnegative {e : ℝ} (he : 0 ≤ e) {z : Node} {ps : List ℕ}
    (hs : Valid z.side z.ratio) (hp : allowed w ell S z ps) : 0 ≤ nodeProduct e w z ps := by
  induction ps generalizing z with
  | nil => exact zero_le_one
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hrest⟩
    change 0 ≤ (primeTilt w z.gap z.side z.ratio p / (1+e)) * nodeProduct e w (step w z p) ps
    exact mul_nonneg (div_nonneg (primeTilt_nonneg hs hchild) (by linarith)) (ih (child_valid hs hchild) hrest)

theorem pathLaw_singleton_weight (hs : Valid start.side start.ratio) (h : History w ell S start) :
    pathLaw w ell S start h.primes.length {some h} = ENNReal.ofReal (nodeProduct (epsilon w) w start h.primes) := by
  classical
  have main : ∀ ps : List ℕ, ∀ h : History w ell S start, h.primes = ps →
      pathLaw w ell S start ps.length {some h} = ENNReal.ofReal (nodeProduct (epsilon w) w start ps) := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil =>
      intro h heq
      have hh : h = History.empty := History.ext heq
      subst h
      change Measure.dirac (some (History.empty : History w ell S start)) {some History.empty} = ENNReal.ofReal (1 : ℝ)
      simp
    | append_singleton ps p ih =>
      intro h heq
      have hall : allowed w ell S start (ps++[p]) := heq ▸ h.admissible
      obtain ⟨hpre,hlast⟩ := (allowed_append w ell S start ps [p]).mp hall
      let g : History w ell S start := ⟨ps,hpre⟩
      have hp : p ∈ nodeChildren w ell S g.node := (allowed_cons w ell S g.node p []).mp hlast |>.1
      have hh : h = g.append p hp := History.ext heq
      rw [hh, List.length_append, List.length_singleton, pathLaw_append, ih g rfl, nodeProduct_append]
      have hgn : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
      have hn : 0 ≤ primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w) :=
        div_nonneg (primeTilt_nonneg (w := w) (r := g.node.gap) (i := g.node.side) (s := g.node.ratio) hgn hp) (normalizer_pos w).le
      change ENNReal.ofReal (primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w)) *
          ENNReal.ofReal (nodeProduct (epsilon w) w start ps) =
        ENNReal.ofReal (nodeProduct (epsilon w) w start ps *
          (primeTilt w g.node.gap g.node.side g.node.ratio p / (1+epsilon w) * 1))
      rw [← ENNReal.ofReal_mul hn]
      congr 1
      ring
  exact main h.primes h rfl

theorem source_prime_weight_identity (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (h : History w ell S start) :
    ErdosPrimeInputs.PrimePrefixMass.prefixWeight h.primes =
      (pathLaw w ell S start h.primes.length {some h}).toReal * (1+epsilon w)^h.primes.length *
        (h.node.gap/start.gap)^2 * (weight start.side start.ratio / weight h.node.side h.node.ratio) := by
  rw [pathLaw_singleton_weight hs h, ENNReal.toReal_ofReal (nodeProduct_nonnegative (epsilon_pos w).le hs h.admissible)]
  have hweight := normalized_prime_prefix_weight_identity (epsilon_pos w).le hell hr hs h.admissible
  simpa only [nodeProduct, History.node, terminal_gap_eq, terminal_side_eq, terminal_ratio_eq] using hweight

end NumberTheoryLean.PrimeChainProbabilities



namespace NumberTheoryLean.PrimeHistoryHorizon

open _root_.Set _root_.Finset
open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open LowStateHorizon ErdosPrimeInputs.HarmonicPrimeMeasure

theorem valid_ratio_lower {i : Side} {t : ℝ} (ht : Valid i t) : (19/20 : ℝ) ≤ t := by
  cases i <;> dsimp [Valid] at ht <;> linarith

theorem prime_cost_lower {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hs : Valid i s) (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    (ps.length : ℝ)/(S+1) ≤ pathCost (primeRatios w r ps) := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => simp [primeRatios,pathCost]
  | cons p ps ih =>
    rcases hpath with ⟨hp,hrest⟩
    have ht := valid_pos (child_valid hs hp)
    have htS : childRatio w r p ≤ S := (Finset.mem_filter.mp hp).2.2.2.2
    have hc : 1/(S+1) ≤ cost (childRatio w r p) :=
      (one_div_le_one_div_of_le (by linarith : 0 < childRatio w r p+1) (by linarith)).trans
        (cost_ge_inv_add_one ht)
    have hih := ih (child_valid hs hp) hrest
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_div, primeRatios, pathCost]
    linarith

theorem prime_gap_cost {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    primeFinalGap w r ps = r * Real.exp (-pathCost (primeRatios w r ps)) := by
  rw [primeFinalGap_eq hell hr hs hpath, finalGap_eq_cost hs (ratios_admissible hpath)]

theorem prime_final_gap_lower {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 < ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) (hne : ps ≠ []) :
    (19/20 : ℝ)*ell < primeFinalGap w r ps := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    rcases hpath with ⟨hp,hrest⟩
    cases ps with
    | nil =>
      have hx : ell < primeExponent w p := (Finset.mem_filter.mp hp).2.1
      have hx0 : 0 < primeExponent w p := hell.trans hx
      have ht := valid_ratio_lower (child_valid hs hp)
      have heq : r-primeExponent w p = childRatio w r p * primeExponent w p := by
        unfold childRatio
        field_simp
      change (19/20 : ℝ)*ell < r-primeExponent w p
      calc
        _ < (19/20 : ℝ)*primeExponent w p := mul_lt_mul_of_pos_left hx (by norm_num)
        _ ≤ childRatio w r p * primeExponent w p := mul_le_mul_of_nonneg_right ht hx0.le
        _ = _ := heq.symm
    | cons q qs =>
      exact ih (child_gap_positive hell.le hr hs hp) (child_valid hs hp) hrest (by simp)

theorem prime_source_horizon {w ell S s r cap B : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 1 ≤ ell) (hS : 0 ≤ S) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) (hB : 0 < B) (hsize : r ≤ (23/10 : ℝ)*B) :
    ps.length < sourceHorizon S B := by
  by_cases hne : ps = []
  · subst ps
    unfold sourceHorizon
    simp
  · have hell0 : 0 < ell := by linarith
    have hgap := prime_final_gap_lower hell0 hr hs hpath hne
    have hl := Real.log_lt_log (mul_pos (by norm_num : (0 : ℝ) < 19/20) hell0) hgap
    rw [prime_gap_cost hell0.le hr hs hpath,
      Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    have hc := prime_cost_lower hs hpath
    have hlogR := Real.log_le_log hr hsize
    rw [Real.log_mul (by norm_num : (23/10 : ℝ) ≠ 0) hB.ne'] at hlogR
    have hlog23 : Real.log (23/10 : ℝ) ≤ 13/10 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 23/10)
      norm_num at h
      exact h
    have hlog19 : (-1/19 : ℝ) ≤ Real.log (19/20 : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 19/20)
      norm_num at h
      linarith
    have hlogell : Real.log (19/20 : ℝ) ≤ Real.log ((19/20 : ℝ)*ell) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    have hn : (ps.length : ℝ)/(S+1) < Real.log B+2 := by linarith
    have hmul := (div_lt_iff₀ (by linarith : 0 < S+1)).mp hn
    have hceil := Nat.le_ceil ((S+1)*(Real.log B+2))
    have hreal : (ps.length : ℝ) < (sourceHorizon S B : ℝ) := by
      unfold sourceHorizon
      push_cast
      nlinarith
    exact_mod_cast hreal

theorem history_length_lt {w ell S B : ℝ} {start : Node}
    (hell : 1 ≤ ell) (hS : 0 ≤ S) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (h : History w ell S start) :
    h.primes.length < sourceHorizon S B :=
  prime_source_horizon hell hS hr hs h.admissible hB hsize

end NumberTheoryLean.PrimeHistoryHorizon



namespace NumberTheoryLean.PrimeChainHorizon

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeHistoryHorizon LowStateHorizon

variable {w ell S : ℝ} {start : Node}

theorem stage_measurable (n : ℕ) : MeasurableSet {z : ChainState w ell S start | stage n z} := trivial

theorem next_stage (n : ℕ) (z : ChainState w ell S start) (hz : stage n z) :
    ∀ᵐ y ∂chain w ell S start z, stage (n+1) y := by
  classical
  cases z with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (stage_measurable (n+1))).mpr trivial
  | some h =>
    have hlen : h.primes.length = n := hz
    apply ae_iff.mpr
    simp [chain_some, completedLaw, liveLaw, stage, History.append_primes, hlen]

theorem pathLaw_stage (n : ℕ) : ∀ᵐ z ∂pathLaw w ell S start n, stage n z := by
  induction n with
  | zero =>
    change ∀ᵐ z ∂Measure.dirac (some (History.empty : History w ell S start)), stage 0 z
    exact (ae_dirac_iff (stage_measurable 0)).mpr rfl
  | succ n ih =>
    have hp : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
    change ∀ᵐ z ∂((chain w ell S start)^(n+1)) (some History.empty), stage (n+1) z
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (stage_measurable (n+1))
    filter_upwards [ih] with z hz
    exact next_stage n z hz

end NumberTheoryLean.PrimeChainHorizon



namespace NumberTheoryLean.PrimeCorrectionFactor

open _root_.Filter _root_.Set
open _root_.Erdos970.Filter _root_.Erdos970.Set
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeHistoryHorizon PrimeKilledChain LowStateHorizon

theorem correctionBudget_tendsto_zero (d : ℝ) : Tendsto (correctionBudget d) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => 5*d^3*x^6*Real.exp (-normalizationRate*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (6 : ℝ) normalizationRate normalizationRate_pos).const_mul (5*d^3)
    simpa only [Real.rpow_ofNat, mul_assoc, mul_zero] using h
  have hi : Tendsto (fun w : ℝ => 5*d^3*(Real.log w)^3*epsilon w) atTop (𝓝 0) := by
    apply Tendsto.congr' _ (ht.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with w hw
    have hp : (Real.sqrt (Real.log w))^6 = (Real.log w)^3 := by
      calc
        _ = ((Real.sqrt (Real.log w))^2)^3 := by ring
        _ = _ := by rw [Real.sq_sqrt hw]
    simp only [Function.comp_apply, epsilon, hp]
  have h := ((Real.continuous_exp.tendsto (0 : ℝ)).comp hi).sub_const 1
  change Tendsto (fun w : ℝ => Real.exp (5*d^3*(Real.log w)^3*epsilon w)-1) atTop (𝓝 0)
  simpa only [Function.comp_apply, Real.exp_zero, sub_self] using h

theorem correction_le_budget {d w B : ℝ} (hB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) (n : ℕ)
    (hn : n ≤ sourceHorizon ((Real.log B)^2) B) :
    0 ≤ (1+epsilon w)^n-1 ∧ (1+epsilon w)^n-1 ≤ correctionBudget d w := by
  have hpow1 : 1 ≤ (1+epsilon w)^n := one_le_pow₀ (by linarith [epsilon_pos w])
  have hN := source_horizon_log_cube hB
  have hnR : (n : ℝ) ≤ (sourceHorizon ((Real.log B)^2) B : ℝ) := by exact_mod_cast hn
  have hcube : (Real.log B)^3 ≤ (d*Real.log w)^3 := pow_le_pow_left₀ (by linarith) hcomp 3
  have hnum : (n : ℝ) ≤ 5*d^3*(Real.log w)^3 := by nlinarith [hN,hnR]
  have hbase : 1+epsilon w ≤ Real.exp (epsilon w) := by
    simpa only [add_comm] using Real.add_one_le_exp (epsilon w)
  have hp : (1+epsilon w)^n ≤ (Real.exp (epsilon w))^n := pow_le_pow_left₀ (by linarith [epsilon_pos w]) hbase n
  rw [← Real.exp_nat_mul] at hp
  have he : Real.exp ((n : ℝ)*epsilon w) ≤ Real.exp (5*d^3*(Real.log w)^3*epsilon w) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnum (epsilon_pos w).le)
  exact ⟨sub_nonneg.mpr hpow1, sub_le_sub_right (hp.trans he) 1⟩

theorem history_correction {d w ell B : ℝ} {start : Node}
    (hlogB : 2 ≤ Real.log B)
    (hcomp : Real.log B ≤ d*Real.log w) (hell : 1 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B)
    (h : History w ell ((Real.log B)^2) start) :
    0 ≤ (1+epsilon w)^h.primes.length-1 ∧
      (1+epsilon w)^h.primes.length-1 ≤ correctionBudget d w :=
  correction_le_budget hlogB hcomp h.primes.length
    (history_length_lt hell (sq_nonneg _) hr hs hB hsize h).le

end NumberTheoryLean.PrimeCorrectionFactor



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCompactWeights
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeBinMembership

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open PrimeRatioBins NormalizedPrimeBins PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem step_consistent {w ell S : ℝ} {z : Node} {p : ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hp : p ∈ nodeChildren w ell S z) :
    Consistent (step w z p) := by
  have hx := child_exponent_positive hell hp
  have ht := valid_pos (child_valid hs hp)
  change primeExponent w p = (z.gap-primeExponent w p)/childRatio w z.gap p
  rw [← nextGap_childRatio hr hx ht, nextGap_div_ratio ht, nextExponent_childRatio hr hx]

theorem terminal_consistent {w ell S : ℝ} {z : Node} {ps : List ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hz : Consistent z) (hp : allowed w ell S z ps) :
    Consistent (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hc,ht⟩
    exact ih (child_gap_positive hell hr hs hc) (child_valid hs hc) (step_consistent hell hr hs hc) ht

end NumberTheoryLean.PrimeBinMembership

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

theorem uncapped_gap_positive {w ell : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hp : uncappedAllowed w ell z ps) : 0 < (terminal w z ps).gap := by
  obtain ⟨U,_,hU⟩ := (uncapped_iff_exists_ceiling w ell z ps).mp hp
  exact terminal_gap_positive hell hr hs hU

end NumberTheoryLean.ActualPrimeHigh

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open FinitePathGeometry PrimeHistories PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ActualPrimeHigh

theorem sum_histories {w ell S : ℝ} (hw : 1 < w) (start : Node) (F : List ℕ → ℝ) :
    letI := historyFintype (ell := ell) (S := S) hw start
    (∑ h : History w ell S start,F h.primes) =
      ∑ ps ∈ retainedPrefixes w ell S start,F ps := by
  classical
  let := historyFintype (ell := ell) (S := S) hw start
  calc
    _ = ∑ ps : {ps // ps ∈ retainedPrefixes w ell S start},F ps.val :=
      (Equiv.sum_comp (retainedHistoryEquiv hw start) (fun h => F h.primes)).symm
    _ = _ := Finset.sum_attach _ F

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.PrimeCompactWeights

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open PrimeCorrectionFactor PrimeBinMembership PrimeTiltGeometry DerivativeWeights

theorem scaledWeight_nonneg {w B ell S : ℝ} {start : Node}
    (hs : Valid start.side start.ratio) (z : ChainState w ell S start) : 0 ≤ scaledWeight w B start z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hφ := (weight_pos hs).le
    have hφ' := (weight_pos (terminal_valid hs h.admissible)).le
    have he := (normalizer_pos w).le
    unfold scaledWeight
    positivity

end NumberTheoryLean.PrimeCompactWeights

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ReferenceHistoryAdmission
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceHistoryAdmission

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission ReferencePruning ReferencePrefixRecurrence ReferenceSourcePrimeSets ReferenceEulerRecurrence
open ReferenceCancellation
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem cap_lower_ratio {w : ℝ} {z : Node} {p : ℕ} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hx : 0 < primeExponent w p) (hcap : capGuard z.closed z.cutoff (primeExponent w p)) :
    z.ratio-1 ≤ childRatio w z.gap p := by
  have hxp : primeExponent w p ≤ z.cutoff := by
    cases hcl : z.closed with
    | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
               exact h.le
    | true => simpa [capGuard,hcl] using hcap
  have he := (eq_div_iff (ne_of_gt (valid_pos hs))).mp hz
  have hm := mul_le_mul_of_nonneg_right hxp (valid_pos hs).le
  have hd : z.ratio ≤ z.gap/primeExponent w p := (le_div_iff₀ hx).mpr (by nlinarith)
  unfold childRatio
  linarith

theorem uncapped_child_iff {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hz : Consistent z) (p : ℕ) :
    p ∈ uncappedChildren w 2 z ↔ p ∈ highPrimes w z.cutoff z.closed ∧
      childAdmitted z.side z.gap (primeExponent w p) := by
  constructor
  · intro hp
    obtain ⟨hprime,hx,hcap,hmin⟩ := Finset.mem_filter.mp hp
    have hpP := (Nat.mem_primesLE.mp hprime).2
    refine ⟨(highPrimes_membership hw z.cutoff z.closed p).mpr ⟨hpP,hx,hcap⟩,?_⟩
    cases hi : z.side with
    | even => trivial
    | odd =>
      rw [hi] at hmin
      apply (upper_admission_above_two hx.le).mpr
      have h2 : 2 ≤ childRatio w z.gap p := (le_max_left _ _).trans hmin
      have hdiv : 3 ≤ z.gap/primeExponent w p := by unfold childRatio at h2; linarith
      have hm := (le_div_iff₀ (by linarith : 0 < primeExponent w p)).mp hdiv
      linarith
  · rintro ⟨hp,ha⟩
    obtain ⟨hpP,hx,hcap⟩ := (highPrimes_membership hw z.cutoff z.closed p).mp hp
    have hx0 : 0 < primeExponent w p := by linarith
    have hxp : primeExponent w p ≤ z.cutoff := by
      cases hcl : z.closed with
      | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
                 exact h.le
      | true => simpa [capGuard,hcl] using hcap
    have hpLe := (exponent_le_iff hw (by exact_mod_cast hpP.pos)).mp hxp
    have hprime := Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) z.cutoff).le).mpr hpLe,hpP⟩
    apply Finset.mem_filter.mpr
    refine ⟨hprime,hx,hcap,?_⟩
    have hlo := cap_lower_ratio hs hz hx0 hcap
    cases hi : z.side with
    | even => exact hlo
    | odd =>
      rw [hi] at ha
      apply max_le
      · have hh := (upper_admission_above_two hx.le).mp ha
        unfold childRatio
        have hd : 3 ≤ z.gap/primeExponent w p := (le_div_iff₀ hx0).mpr (by linarith)
        linarith
      · exact hlo

theorem uncapped_child_invariants {w : ℝ} {z : Node} {p : ℕ}
    (hs : Valid z.side z.ratio) (hr : 0 < z.gap) (hp : p ∈ uncappedChildren w 2 z) :
    Valid (step w z p).side (step w z p).ratio ∧ 0 < (step w z p).gap ∧ Consistent (step w z p) := by
  have hone : uncappedAllowed w 2 z [p] := ⟨hp,trivial⟩
  obtain ⟨U,_hU,hU⟩ := (uncapped_iff_exists_ceiling w 2 z [p]).mp hone
  have hc := ((allowed_cons w 2 U z p []).mp hU).1
  exact ⟨child_valid hs hc,child_gap_positive (by norm_num) hr hs hc,step_consistent (by norm_num) hr hs hc⟩

theorem decreasing_cons_iff (P : Finset ℕ) (p : ℕ) (ps : List ℕ) :
    p::ps ∈ decreasingPrefixes P ↔ p ∈ P ∧ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)) := by
  constructor
  · intro h
    have hp := (mem_decreasingPrefixes.mp h).2 p (by simp)
    refine ⟨hp,?_⟩
    have ht := (append_mem_decreasing_iff (singleton_prefix_mem hp)).mp h
    simpa [suffixPrimes] using ht
  · rintro ⟨hp,ht⟩
    apply (append_mem_decreasing_iff (singleton_prefix_mem hp)).mpr
    simpa [suffixPrimes] using ht

theorem referencePrefixes_cons_iff (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (p : ℕ) (ps : List ℕ) :
    p::ps ∈ referencePrefixes w P i r ↔ p ∈ P ∧ childAdmitted i r (primeExponent w p) ∧
      ps ∈ referencePrefixes w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) := by
  simp only [referencePrefixes,Finset.mem_filter,decreasing_cons_iff,admitted]
  tauto

theorem reference_history_iff {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) (ps : List ℕ) :
    ps ∈ referencePrefixes w (highPrimes w z.cutoff z.closed) z.side z.gap ↔ uncappedAllowed w 2 z ps := by
  induction ps generalizing z with
  | nil => simp [referencePrefixes,mem_decreasingPrefixes,admitted,uncappedAllowed]
  | cons p ps ih =>
    rw [referencePrefixes_cons_iff]
    constructor
    · rintro ⟨hp,ha,ht⟩
      have hpU := (uncapped_child_iff hw hs hz p).mpr ⟨hp,ha⟩
      obtain ⟨hvs,hrs,hzs⟩ := uncapped_child_invariants hs hr hpU
      have hpS : p ∈ sourcePrimes w z.cutoff z.closed := (Finset.mem_filter.mp hp).1
      have he := highPrimes_at_selected hw z.closed hpS
      rw [← he] at ht
      exact ⟨hpU,(ih hvs hrs hzs).mp ht⟩
    · rintro ⟨hpU,htU⟩
      obtain ⟨hp,ha⟩ := (uncapped_child_iff hw hs hz p).mp hpU
      obtain ⟨hvs,hrs,hzs⟩ := uncapped_child_invariants hs hr hpU
      have ht := (ih hvs hrs hzs).mpr htU
      have hpS : p ∈ sourcePrimes w z.cutoff z.closed := (Finset.mem_filter.mp hp).1
      have he := highPrimes_at_selected hw z.closed hpS
      change ps ∈ referencePrefixes w (highPrimes w (primeExponent w p) false) z.side.flip (z.gap-primeExponent w p) at ht
      rw [he] at ht
      exact ⟨hp,ha,ht⟩

theorem reference_family_eq_uncapped {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) :
    referencePrefixes w (highPrimes w z.cutoff z.closed) z.side z.gap=uncappedPrefixes w 2 z := by
  ext ps
  rw [reference_history_iff hw hs hr hz,mem_uncappedPrefixes hw]

end NumberTheoryLean.ReferenceHistoryAdmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExponentialMesh
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ExponentialMesh

open _root_.Set _root_.Filter
open scoped Topology

theorem log_pow_sqrt (n : ℕ) {w : ℝ} (hw : 0 ≤ Real.log w) :
    (Real.sqrt (Real.log w))^(2*n) = (Real.log w)^n := by
  rw [pow_mul,Real.sq_sqrt hw]

theorem log_power_exp_tendsto (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => C*(Real.log w)^n*Real.exp (-c*Real.sqrt (Real.log w))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => C*x^(2*n)*Real.exp (-c*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*n:ℕ):ℝ) c hc).const_mul C
    simpa only [Real.rpow_natCast,mul_zero,mul_assoc] using h
  apply Tendsto.congr' _ (hbase.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with w hw
  simp only [Function.comp_apply,log_pow_sqrt n hw]

end NumberTheoryLean.ExponentialMesh

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceMarginalRate
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformBudgetRate

open _root_.Set _root_.Filter
open scoped Topology
open UniformFailureBudget ExponentialMesh BudgetPolynomialBound PrimeKilledChain

theorem source_scale_bound {d w B : ℝ} (hW : d^2 ≤ Real.log w)
    (hB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) :
    (Real.log B)^2 ≤ (Real.log w)^3 ∧
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B:ℝ) ≤ 5*d^3*(Real.log w)^3 := by
  have hlog : 0 ≤ Real.log w := (sq_nonneg d).trans hW
  have hpow₂ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 2
  have hpow₃ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 3
  have hmul := mul_le_mul_of_nonneg_right hW (sq_nonneg (Real.log w))
  have hN := LowStateHorizon.source_horizon_log_cube hB
  constructor <;> nlinarith

end NumberTheoryLean.UniformBudgetRate

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_NonnegativeOriginalOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceCompactOccupation

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeCompactVisits PrimeCompactWeights PrimeCorrectionFactor
open FlaggedOccupationBound PersistentFailureFlag ActualProcessCoupling ActualFlaggedCompact

variable {w ell S B : ℝ} {start : Node}

theorem literal_scaled_weight (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (h : History w ell S start) :
    B^2*ErdosPrimeInputs.PrimePrefixMass.prefixWeight h.primes =
      (pathLaw w ell S start h.primes.length {some h}).toReal*scaledWeight w B start (some h) := by
  rw [PrimeChainProbabilities.source_prime_weight_identity hell hr hs h]
  unfold scaledWeight
  ring

end NumberTheoryLean.SourceCompactOccupation

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon
open PrimeCompactWeights SourceCompactOccupation
open ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}

theorem singleton_off_stage (n : ℕ) (h : History w ell S start) (hne : h.primes.length ≠ n) :
    pathLaw w ell S start n {some h} = 0 := by
  have hsub : ({some h} : Set (ChainState w ell S start)) ⊆ {z | ¬stage n z} := by
    intro z hz
    have he : z = some h := hz
    subst z
    exact hne
  exact measure_mono_null hsub (ae_iff.mp (pathLaw_stage n))

theorem singleton_scaled_reward (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (n : ℕ) (h : History w ell S start)
    (F : List ℕ → ℝ) :
    (pathLaw w ell S start n).real {some h} *
      (scaledWeight w B start (some h)*F h.primes) =
      if n = h.primes.length then B^2*prefixWeight h.primes*F h.primes else 0 := by
  classical
  by_cases hn : n = h.primes.length
  · rw [ite_eq_left hn,hn,measureReal_def]
    rw [← mul_assoc,← literal_scaled_weight hell hr hs h]
  · rw [ite_eq_right hn,measureReal_def,singleton_off_stage n h (Ne.symm hn)]
    simp

theorem finite_signed_original_occupation (hw : normalizationThreshold ≤ w)
    (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (F : List ℕ → ℝ) :
    (∑ n ∈ range (LowStateHorizon.sourceHorizon S B),
      ∫ z,scaledWeight w B start z*listReward F z ∂pathLaw w ell S start n) =
      B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps) := by
  classical
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hw
  let := historyFintype (ell := ell) (S := S) hw1 start
  have hterm (n : ℕ) :
      (∫ z,scaledWeight w B start z*listReward F z ∂pathLaw w ell S start n) =
        ∑ h : History w ell S start,
          if n = h.primes.length then B^2*prefixWeight h.primes*F h.primes else 0 := by
    let := pathLaw_isProbability hw hell hS0 hS hr hs hsS n
    rw [integral_fintype Integrable.of_finite,Fintype.sum_option]
    simp only [scaledWeight,listReward,mul_zero,smul_zero,zero_add]
    apply Finset.sum_congr rfl
    intro h _hh
    exact singleton_scaled_reward (by linarith) hr hs n h F
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hlen (h : History w ell S start) : h.primes.length ∈ range (LowStateHorizon.sourceHorizon S B) :=
    mem_range.mpr (PrimeHistoryHorizon.history_length_lt hell hS0 hr hs hB hsize h)
  simp only [Finset.sum_ite_eq',hlen,ite_true, if_true]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [mul_assoc] using sum_histories hw1 start (fun ps => prefixWeight ps*F ps)

end NumberTheoryLean.PrimeFamilyOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceNodeCoordinates
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceNodeCoordinates

open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeBinMembership
open RegeneratingInverseBands ArrivalKernelGeometry SourceLowRemoval
open InvariantInverseWeights DerivativeWeights

theorem node_gap_eq {B : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : start.cutoff=B) : start.gap=B*start.ratio := by
  have he : start.cutoff=start.gap/start.ratio := hcons
  rw [hcut] at he
  exact ((eq_div_iff (valid_pos hs).ne').mp he).symm

theorem source_node_bounds {B : ℝ} (hB : 0 < B) (start : Node)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) :
    Valid start.side start.ratio ∧ 0 < start.gap ∧ B ≤ start.gap ∧ start.gap ≤ (23/10:ℝ)*B := by
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have he := node_gap_eq hs hcons hcut
  refine ⟨hs,?_,?_,?_⟩
  · rw [he]; exact mul_pos hB (valid_pos hs)
  · nlinarith
  · nlinarith

end NumberTheoryLean.SourceNodeCoordinates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CompactSelectedPartition
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeFamilyOccupation
attribute [local instance] Classical.propDecidable
open FinitePathGeometry PrimeHistories PrimeTiltGeometry
open ActualPrimeHigh

theorem retained_no_high {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hsS : start.ratio ≤ S) (hp : allowed w ell S start ps) :
    ¬actualHasHigh w S start ps := by
  rintro ⟨pre,suf,he,hh⟩
  have hpre := (allowed_append w ell S start pre suf).mp (he ▸ hp) |>.1
  exact (not_lt_of_ge (terminal_ratio_le hsS hpre)) hh

theorem allowed_of_uncapped_prefix_ceiling {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hp : uncappedAllowed w ell start ps)
    (hbound : ∀ pre suf : List ℕ, ps = pre++suf → (terminal w start pre).ratio ≤ S) :
    allowed w ell S start ps := by
  classical
  induction ps generalizing start with
  | nil => exact allowed_nil w ell S start
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hpS : (step w start p).ratio ≤ S := by
      simpa only [terminal_cons,terminal_nil] using hbound [p] ps rfl
    have hb : ∀ pre suf : List ℕ, ps = pre++suf →
        (terminal w (step w start p) pre).ratio ≤ S := by
      intro pre suf he
      exact hbound (p::pre) suf (by rw [List.cons_append,he])
    obtain ⟨hprime,hlo,hcap,hmin⟩ := Finset.mem_filter.mp hc
    apply (allowed_cons w ell S start p ps).mpr
    exact ⟨Finset.mem_filter.mpr ⟨hprime,hlo,hcap,hmin,hpS⟩,ih ht hb⟩

theorem allowed_iff_uncapped_no_high {w ell S : ℝ} {start : Node} (hsS : start.ratio ≤ S)
    (ps : List ℕ) : allowed w ell S start ps ↔
      uncappedAllowed w ell start ps ∧ ¬actualHasHigh w S start ps := by
  constructor
  · intro hp
    exact ⟨(uncapped_iff_exists_ceiling w ell start ps).mpr ⟨S,hsS,hp⟩,retained_no_high hsS hp⟩
  · rintro ⟨hp,hh⟩
    apply allowed_of_uncapped_prefix_ceiling hp
    intro pre suf he
    exact le_of_not_gt (fun h => hh ⟨pre,suf,he,h⟩)

theorem retained_eq_nonhigh {w ell S : ℝ} (hw : 1 < w) {start : Node} (hsS : start.ratio ≤ S) :
    retainedPrefixes w ell S start =
      (uncappedPrefixes w ell start).filter (fun ps => ¬actualHasHigh w S start ps) := by
  classical
  ext ps
  rw [mem_retainedPrefixes hw,Finset.mem_filter,mem_uncappedPrefixes hw]
  exact allowed_iff_uncapped_no_high hsS ps

theorem uncapped_sum_partition {w ell S : ℝ} (hw : 1 < w) {start : Node}
    (hsS : start.ratio ≤ S) (F : List ℕ → ℝ) :
    (∑ ps ∈ uncappedPrefixes w ell start,F ps) =
      (∑ ps ∈ retainedPrefixes w ell S start,F ps) +
      ∑ ps ∈ (uncappedPrefixes w ell start).filter (actualHasHigh w S start),F ps := by
  classical
  rw [retained_eq_nonhigh hw hsS]
  exact (Finset.sum_filter_not_add_sum_filter _ _ _).symm

end NumberTheoryLean.PrimeFamilyOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceSourceDecomposition
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualBoundaryDomain

attribute [local instance] Classical.propDecidable

open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ActualPrimeHigh SourceNodeCoordinates
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem child_boundary_domain {w ell : ℝ} {z : Node} {p : ℕ} (hell : 2 ≤ ell)
    (heven : z.side=.even → 2 ≤ z.ratio) (hp : p ∈ uncappedChildren w ell z) :
    BoundaryDomain (step w z p).side (step w z p).gap ∧
      ((step w z p).side=.even → 2 ≤ (step w z p).ratio) := by
  obtain ⟨_hprime,hlo,_hcap,hmin⟩ := Finset.mem_filter.mp hp
  have hx : 2 < primeExponent w p := hell.trans_lt hlo
  have he : (step w z p).ratio*primeExponent w p=(step w z p).gap := by
    dsimp only [step,childRatio]
    field_simp [show primeExponent w p ≠ 0 by linarith]
  cases hi : z.side with
  | even =>
    have hs := heven hi
    have hm : 1 ≤ (step w z p).ratio := by
      change minRatio z.side z.ratio ≤ childRatio w z.gap p at hmin
      rw [hi] at hmin
      change z.ratio-1 ≤ (step w z p).ratio at hmin
      linarith
    have hside : (step w z p).side=.odd := by simp [step,hi,Side.flip]
    rw [hside]
    refine ⟨?_,by intro h; cases h⟩
    change 2 ≤ (step w z p).gap
    nlinarith
  | odd =>
    have hm : 2 ≤ (step w z p).ratio := by
      change minRatio z.side z.ratio ≤ childRatio w z.gap p at hmin
      rw [hi] at hmin
      exact (le_max_left _ _).trans hmin
    have hside : (step w z p).side=.even := by simp [step,hi,Side.flip]
    rw [hside]
    exact ⟨by change 4 ≤ (step w z p).gap; nlinarith,fun _ => hm⟩

theorem boundary_domain_preserved {w ell : ℝ} {z : Node} {ps : List ℕ} (hell : 2 ≤ ell)
    (hdom : BoundaryDomain z.side z.gap) (heven : z.side=.even → 2 ≤ z.ratio)
    (hp : uncappedAllowed w ell z ps) :
    BoundaryDomain (terminal w z ps).side (terminal w z ps).gap := by
  induction ps generalizing z with
  | nil => exact hdom
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    obtain ⟨hd,he⟩ := child_boundary_domain hell heven hc
    exact ih hd he ht

theorem source_boundary_domain {B w ell : ℝ} (hB : 4 ≤ B) (hell : 2 ≤ ell)
    (start : Node) (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hc : Consistent start) (hcut : start.cutoff=B) {ps : List ℕ}
    (hp : uncappedAllowed w ell start ps) :
    BoundaryDomain (terminal w start ps).side (terminal w start ps).gap := by
  obtain ⟨hs,_hr,hBgap,_hsize⟩ := source_node_bounds (by linarith : 0 < B) start hi h199 h23 hc hcut
  have hgap := node_gap_eq hs hc hcut
  cases ps with
  | nil => simpa only [terminal_nil,hi,BoundaryDomain] using hB.trans hBgap
  | cons p ps =>
    obtain ⟨hchild,htail⟩ := hp
    obtain ⟨_hprime,_hlo,hcap,_hmin⟩ := Finset.mem_filter.mp hchild
    have hxp : primeExponent w p ≤ B := by
      change capGuard start.closed start.cutoff (primeExponent w p) at hcap
      rw [hcut] at hcap
      cases hcl : start.closed with
      | false =>
        have h : primeExponent w p < B := by simpa [capGuard,hcl] using hcap
        exact h.le
      | true => simpa only [capGuard,hcl,ite_true, if_true] using hcap
    have hside : (step w start p).side=.odd := by simp [step,hi,Side.flip]
    have hdom : BoundaryDomain (step w start p).side (step w start p).gap := by
      rw [hside]
      change 2 ≤ start.gap-primeExponent w p
      nlinarith
    simpa only [terminal_cons] using boundary_domain_preserved (z := step w start p) hell hdom (by rw [hside]; intro h; cases h) htail

end NumberTheoryLean.ActualBoundaryDomain

end

section

namespace NumberTheoryLean.ReferenceSourceDecomposition

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission ReferencePruning ReferenceWeightedRecurrence ReferenceForestTelescoping ReferenceCutoffRecurrence
open ReferenceSourcePrimeSets ReferenceEulerRecurrence ReferenceHistoryAdmission ReferenceLocalResidual
open BoundaryAnomaly UniformBoundaryCorrection
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem suffix_highPrimes {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) {ps : List ℕ} (hp : uncappedAllowed w 2 z ps) :
    suffixPrimes (highPrimes w z.cutoff z.closed) ps=
      highPrimes w (terminal w z ps).cutoff (terminal w z ps).closed := by
  induction ps generalizing z with
  | nil => simp only [suffixPrimes_nil,terminal_nil]
  | cons p ps ih =>
    obtain ⟨hchild,htail⟩ := hp
    have hpH := ((uncapped_child_iff hw hs hz p).mp hchild).1
    have hpS : p ∈ sourcePrimes w z.cutoff z.closed := (Finset.mem_filter.mp hpH).1
    obtain ⟨hvs,hrs,hzs⟩ := uncapped_child_invariants hs hr hchild
    rw [suffixPrimes_cons,terminal_cons,← highPrimes_at_selected hw z.closed hpS]
    exact ih (z := step w z p) hvs hrs hzs htail

theorem uncapped_cutoff_gt_two {w : ℝ} {z : Node} (hb : 2 < z.cutoff) {ps : List ℕ}
    (hp : uncappedAllowed w 2 z ps) : 2 < (terminal w z ps).cutoff := by
  induction ps generalizing z with
  | nil => exact hb
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hx : 2 < primeExponent w p := (Finset.mem_filter.mp hc).2.1
    exact ih hx ht

theorem forest_insertion_eq_corrections {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) (hb : 2 < z.cutoff) :
    forestSum w (highPrimes w z.cutoff z.closed) z
      (cutoffInsertion w (boundaryPrimes w) (fun _ y => nodeBenchmark w y))=
      boundaryCorrection w 2 z+residualCorrection w z := by
  unfold forestSum weightedValue boundaryCorrection residualCorrection
  rw [reference_family_eq_uncapped hw hs hr hz,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ps hp
  have hpA : uncappedAllowed w 2 z ps := (Finset.mem_filter.mp hp).2
  have hsuf := suffix_highPrimes hw hs hr hz hpA
  have hcap := uncapped_cutoff_gt_two hb hpA
  dsimp only
  rw [hsuf]
  change signedWeight ps*sourceInsertion w (terminal w z ps)=_
  rw [source_insertion_identity hw _ hcap]
  unfold signedWeight
  ring

theorem actual_reference_decomposition {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) (hb : 2 < z.cutoff) :
    sourceReference w z-nodeBenchmark w z=boundaryCorrection w 2 z+residualCorrection w z := by
  have h := finite_cutoff_decomposition w (highPrimes_above_boundary (b:=z.cutoff) hw z.closed)
    (fun _ y => nodeBenchmark w y) z
  rw [← sourcePrimes_partition hw hb z.closed] at h
  exact h.trans (forest_insertion_eq_corrections hw hs hr hz hb)

end NumberTheoryLean.ReferenceSourceDecomposition

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_MovingLocalReference
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.ReferenceProductErrorBounds

open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceMertens ReferenceSourcePrimeSets ReferenceBenchmarkDecay ReferenceDifferentiation
open ReferenceResidualErrors
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem primeError_pos (c w t : ℝ) : 0 < primeError c w t := Real.exp_pos _

end NumberTheoryLean.ReferenceProductErrorBounds



namespace NumberTheoryLean.ReferenceLogScale

open _root_.Filter
open scoped Topology
open ReferenceProductErrorBounds ExponentialMesh

theorem primeError_two_eq (c w : ℝ) :
    primeError c w 2=Real.exp (-(c*Real.sqrt 2)*Real.sqrt (Real.log w)) := by
  unfold primeError
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem log_power_primeError_tendsto (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => C*(Real.log w)^n*primeError c w 2) atTop (𝓝 0) := by
  have h := log_power_exp_tendsto C n (mul_pos hc (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  simpa only [primeError_two_eq] using h

end NumberTheoryLean.ReferenceLogScale



namespace NumberTheoryLean.ReferenceResidualSum

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry ActualPrimeHigh ActualBoundaryDomain
open SourceNodeCoordinates ReferenceSourceDecomposition ReferenceProductErrorBounds
open ReferenceLocalResidual TwoStepDensityBounds
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem uncapped_cutoff_le {w : ℝ} {z : Node} {ps : List ℕ} (hp : uncappedAllowed w 2 z ps) :
    (terminal w z ps).cutoff ≤ z.cutoff := by
  induction ps generalizing z with
  | nil => exact le_rfl
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hcap := (Finset.mem_filter.mp hc).2.2.1
    have hx : ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p ≤ z.cutoff := by
      cases hcl : z.closed with
      | false => have h : ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
                 exact h.le
      | true => simpa [capGuard,hcl] using hcap
    exact (ih (z:=step w z p) ht).trans hx

theorem signed_residual_le_absolute (w : ℝ) (start : Node) :
    |residualCorrection w start| ≤ residualAbsoluteSum w start := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ps _hp
  simp only [abs_mul,abs_of_nonneg (prefixWeight_nonneg ps),abs_pow,abs_neg,abs_one,one_pow,one_mul]
  exact le_rfl

end NumberTheoryLean.ReferenceResidualSum



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Conclusions_JacobsthalSourceScale
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.JacobsthalSourceScale

open _root_.Filter _root_.Asymptotics
open scoped Topology

theorem log_square_le_sqrt_eventually : ∀ᶠ L : ℝ in atTop,(Real.log L)^2 ≤ Real.sqrt L := by
  have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s:=1/2) (by norm_num)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with L hL hpos
  have hr : 0 ≤ L^((1/2:ℝ)) := Real.rpow_nonneg (by linarith) _
  simpa only [Real.rpow_ofNat,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log L)),
    abs_of_nonneg hr,one_mul,← Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg L)] using hL

theorem sourceW_bounds_eventually : ∀ᶠ L : ℝ in atTop,
    1 < sourceW L ∧ Real.sqrt L ≤ sourceW L ∧ sourceW L ≤ L := by
  filter_upwards [log_square_le_sqrt_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with L hsmall hL hlog
  have hL0 : 0 < L := by linarith
  have hden : 0 < (Real.log L)^2 := sq_pos_of_pos (by linarith)
  have hsq : Real.sqrt L ≤ sourceW L := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg L)
    simpa only [Real.mul_self_sqrt hL0.le] using hm
  have hlow : 1 < Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hL
  refine ⟨hlow.trans_le hsq,hsq,?_⟩
  exact div_le_self hL0.le (by nlinarith : 1 ≤ (Real.log L)^2)

theorem sourceW_tendsto : Tendsto sourceW atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [sourceW_bounds_eventually,Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop R)] with L hW hR
  exact hR.trans hW.2.1

theorem source_scale_eventually : ∀ᶠ L : ℝ in atTop,
    1 < sourceW L ∧ 0 < sourceB L ∧ Real.sqrt L ≤ sourceB L ∧ sourceB L ≤ L ∧
      Real.log (sourceB L) ≤ 2*Real.log (sourceW L) := by
  filter_upwards [sourceW_bounds_eventually,log_square_le_sqrt_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    sourceW_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with L hW hsmall hL hlog hWexp
  have hL0 : 0 < L := by linarith
  have hW0 : 0 < sourceW L := by linarith [hW.1]
  have hlogW : 1 ≤ Real.log (sourceW L) := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hWexp
  have hlogWL : Real.log (sourceW L) ≤ Real.log L := Real.log_le_log hW0 hW.2.2
  have hlogSmall : Real.log (sourceW L) ≤ Real.sqrt L := by
    have hh : Real.log L ≤ (Real.log L)^2 := by nlinarith
    exact hlogWL.trans (hh.trans hsmall)
  have hBpos : 0 < sourceB L := div_pos hL0 (by linarith)
  have hBsq : Real.sqrt L ≤ sourceB L := by
    apply (le_div_iff₀ (show 0 < Real.log (sourceW L) by linarith)).mpr
    have hm := mul_le_mul_of_nonneg_left hlogSmall (Real.sqrt_nonneg L)
    simpa only [Real.mul_self_sqrt hL0.le] using hm
  have hBL : sourceB L ≤ L := div_le_self hL0.le hlogW
  have hLWsq : L ≤ (sourceW L)^2 := by
    have hh := mul_self_le_mul_self (Real.sqrt_nonneg L) hW.2.1
    nlinarith [Real.sq_sqrt hL0.le]
  have hcomp := Real.log_le_log hBpos (hBL.trans hLWsq)
  refine ⟨hW.1,hBpos,hBsq,hBL,?_⟩
  simpa only [Real.log_pow,Nat.cast_ofNat] using hcomp

theorem sourceB_tendsto : Tendsto sourceB atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [source_scale_eventually,Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop R)] with L h hR
  exact hR.trans h.2.2.1

end NumberTheoryLean.JacobsthalSourceScale

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CorrectionFloorRemainder
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.JacobsthalSourceScale

theorem paper_ratio_tendsto (a : ℝ) {e : ℝ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun L => paperGap a e L/sourceB L) atTop (𝓝 2) := by
  have hn : Tendsto (fun L : ℝ => (-a+2+e L)/sourceB L) atTop (𝓝 0) :=
    ((tendsto_const_nhds.add he).div_atTop sourceB_tendsto)
  have hl : Tendsto (fun L : ℝ => Real.log L/L) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have ht : Tendsto (fun L : ℝ => 2+(-a+2+e L)/sourceB L-2*(Real.log L/L)) atTop (𝓝 2) := by
    simpa only [add_zero,mul_zero,sub_zero] using (tendsto_const_nhds.add hn).sub (hl.const_mul 2)
  apply ht.congr'
  filter_upwards [source_scale_eventually,eventually_gt_atTop (0:ℝ)] with L hs hL
  have hw : Real.log (sourceW L) ≠ 0 := (Real.log_pos hs.1).ne'
  unfold paperGap sourceB
  field_simp
  ring

end ErdosCorrectionLimit

end

section

open _root_.Filter
open scoped Topology
namespace ErdosCorrectionLimit
open NumberTheoryLean.JacobsthalSourceScale

theorem unroundedY_tendsto : Tendsto unroundedY atTop atTop := by
  simpa only [unroundedY,Real.rpow_two] using! tendsto_exp_mul_div_rpow_atTop 2 2 (by norm_num)

theorem floor_log_error_tendsto :
    Tendsto (fun L => Real.log (⌊unroundedY L⌋₊ : ℝ)-(2*L-2*Real.log L)) atTop (𝓝 0) := by
  have hratio := (tendsto_nat_floor_div_atTop (R := ℝ)).comp unroundedY_tendsto
  have hh := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hratio
  simp only [Real.log_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),unroundedY_tendsto.eventually (eventually_ge_atTop (2:ℝ))] with L hL hY
  have hYpos : 0 < unroundedY L := by linarith
  have hfloor : 0 < (⌊unroundedY L⌋₊ : ℝ) := by
    exact_mod_cast (Nat.floor_pos.mpr (by linarith : 1 ≤ unroundedY L))
  have hL0 : L ≠ 0 := by linarith
  change Real.log ((⌊unroundedY L⌋₊ : ℝ)/unroundedY L)=_
  rw [Real.log_div hfloor.ne' hYpos.ne']
  congr 1
  rw [unroundedY,Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 2 hL0),Real.log_exp,Real.log_pow]
  norm_num

theorem floorRemainder_tendsto : Tendsto floorRemainder atTop (𝓝 0) := by
  exact floor_log_error_tendsto.div_atTop (Real.tendsto_log_atTop.comp sourceW_tendsto)

theorem sourceY_exp (L : ℝ) :
    ErdosInverseBoxHeight.sourceY (Real.exp L)=⌊unroundedY L⌋₊ := by
  unfold ErdosInverseBoxHeight.sourceY unroundedY
  rw [Real.log_exp,pow_two,← Real.exp_add]
  congr 2
  ring_nf

theorem paperGap_floor_eq (a : ℝ) {L : ℝ} (hW : 1 < sourceW L) :
    paperGap a floorRemainder L=
      Real.log (ErdosInverseBoxHeight.sourceY (Real.exp L):ℝ)/Real.log (sourceW L)-a+2 := by
  rw [sourceY_exp]
  have hw0 : Real.log (sourceW L) ≠ 0 := (Real.log_pos hW).ne'
  unfold paperGap floorRemainder sourceB
  field_simp
  ring

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_PaperContinuousCorrection
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeBinMembership NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.JacobsthalSourceScale
open Erdos970Dependency.InvariantCostBound

theorem paper_start_eventually (a : ℝ) (closed : Bool) {e : ℝ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    ∀ᶠ L : ℝ in atTop,
      0 < sourceB L ∧ 1 < sourceW L ∧
      Real.log (sourceB L) ≤ 2*Real.log (sourceW L) ∧
      199/100 ≤ (paperStart a e closed L).ratio ∧ (paperStart a e closed L).ratio ≤ 23/10 ∧
      0 < (paperStart a e closed L).gap ∧ Consistent (paperStart a e closed L) := by
  have hr := (paper_ratio_tendsto a he).eventually
    (Ioo_mem_nhds (by norm_num : (199:ℝ)/100 < 2) (by norm_num : (2:ℝ) < 23/10))
  filter_upwards [source_scale_eventually,hr] with L hs hr
  have hB : 0 < sourceB L := hs.2.1
  have hg : 0 < paperGap a e L := by
    have hh := (lt_div_iff₀ hB).mp hr.1
    nlinarith
  refine ⟨hB,hs.1,hs.2.2.2.2,hr.1.le,hr.2.le,hg,?_⟩
  change sourceB L=paperGap a e L/(paperGap a e L/sourceB L)
  field_simp

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_RetainedNormalizedReward
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Finset
namespace ErdosRetainedRewardTransfer
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeKilledChain NumberTheoryLean.PrimeCompactWeights
open NumberTheoryLean.PrimeCorrectionFactor NumberTheoryLean.PrimeFamilyOccupation
open NumberTheoryLean.SourceNodeCoordinates
open NumberTheoryLean.PrimeBinMembership
open ErdosPrimeInputs.PrimePrefixMass

theorem transferConstant_positive : 0 < transferConstant := by
  unfold transferConstant
  exact mul_pos (by norm_num) (weight_pos (by norm_num [Valid]))

theorem scaled_normalized_reward_bound {d w ell B delta : ℝ} {start : Node}
    (hB : 0 < B) (hell : 1 ≤ ell) (hlogB : 2 ≤ Real.log B)
    (hcomp : Real.log B ≤ d*Real.log w) (hbudget : correctionBudget d w ≤ 1)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) (_hdelta : 0 ≤ delta)
    (h : History w ell ((Real.log B)^2) start) (F : List ℕ → ℝ)
    (hF : h.node.gap^2*|F h.primes|/weight h.node.side h.node.ratio ≤ delta) :
    scaledWeight w B start (some h)*|F h.primes| ≤ transferConstant*delta := by
  obtain ⟨hs,hr,hBr,hsize⟩ := source_node_bounds hB start hi h199 h23 hcons hcut
  have hphi : 0 < weight h.node.side h.node.ratio := weight_pos (terminal_valid hs h.admissible)
  have hp0 : 0 ≤ weight start.side start.ratio := (weight_pos hs).le
  have hW : 0 ≤ weight .even (199/100) := (weight_pos (by norm_num [Valid])).le
  have hinit : weight start.side start.ratio ≤ weight .even (199/100) := by
    rw [hi]
    exact NumberTheoryLean.TwoStepDensityBounds.weight_antitone (by norm_num [Valid]) (hi ▸ hs) h199
  have hc : (1+epsilon w)^h.primes.length ≤ 2 := by
    have hh := (history_correction hlogB hcomp hell hr hs hB hsize h).2
    linarith
  have hc0 : 0 ≤ (1+epsilon w)^h.primes.length := pow_nonneg (normalizer_pos w).le _
  have hratio : 0 ≤ B/start.gap := div_nonneg hB.le hr.le
  have hratio1 : B/start.gap ≤ 1 := (div_le_one hr).mpr hBr
  have hsq : (B/start.gap)^2 ≤ 1 := by nlinarith
  have hF0 : 0 ≤ h.node.gap^2*|F h.primes|/weight h.node.side h.node.ratio := by positivity
  calc
    _ = ((B/start.gap)^2*(1+epsilon w)^h.primes.length*weight start.side start.ratio)*
        (h.node.gap^2*|F h.primes|/weight h.node.side h.node.ratio) := by unfold scaledWeight; ring
    _ ≤ (1*2*weight .even (199/100))*delta :=
      mul_le_mul (mul_le_mul (mul_le_mul hsq hc hc0 (by norm_num)) hinit hp0 (by norm_num)) hF hF0 (by positivity)
    _ = _ := by unfold transferConstant; ring

theorem retained_normalized_reward_sum {d w ell B delta : ℝ} {start : Node}
    (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS : (Real.log B)^2 ≤ (Real.log w)^3) (hsS : start.ratio ≤ (Real.log B)^2)
    (hB : 0 < B) (hlogB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w)
    (hbudget : correctionBudget d w ≤ 1)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) (hdelta : 0 ≤ delta) (F : List ℕ → ℝ)
    (hF : ∀ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,
      (terminal w start ps).gap^2*|F ps|/weight (terminal w start ps).side (terminal w start ps).ratio ≤ delta) :
    B^2*(∑ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,prefixWeight ps*|F ps|) ≤
      transferConstant*(NumberTheoryLean.LowStateHorizon.sourceHorizon ((Real.log B)^2) B : ℝ)*delta := by
  classical
  obtain ⟨hs,hr,_hBr,hsize⟩ := source_node_bounds hB start hi h199 h23 hcons hcut
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hw
  let := historyFintype (ell:=ell) (S:=(Real.log B)^2) hw1 start
  have hpoint (z : ChainState w ell ((Real.log B)^2) start) :
      ‖scaledWeight w B start z*listReward (fun ps => |F ps|) z‖ ≤ transferConstant*delta := by
    cases z with
    | none =>
      simp only [scaledWeight,listReward,mul_zero,norm_zero]
      exact mul_nonneg transferConstant_positive.le hdelta
    | some h =>
      have hnorm : 0 ≤ scaledWeight w B start (some h)*|F h.primes| :=
        mul_nonneg (scaledWeight_nonneg hs _) (abs_nonneg _)
      change ‖scaledWeight w B start (some h)*|F h.primes|‖ ≤ transferConstant*delta
      rw [Real.norm_of_nonneg hnorm]
      apply scaled_normalized_reward_bound hB hell hlogB hcomp hbudget hi h199 h23 hcons hcut hdelta h F
      exact hF h.primes ((mem_retainedPrefixes hw1 start h.primes).mpr h.admissible)
  have hterm (n : ℕ) :
      (∫ z,scaledWeight w B start z*listReward (fun ps => |F ps|) z ∂pathLaw w ell ((Real.log B)^2) start n) ≤
        transferConstant*delta := by
    let := pathLaw_isProbability hw hell (sq_nonneg _) hS hr hs hsS n
    have hn := norm_integral_le_of_norm_le_const (μ:=pathLaw w ell ((Real.log B)^2) start n)
      (Filter.Eventually.of_forall hpoint)
    rw [Real.norm_eq_abs] at hn
    have hle := le_abs_self (∫ z,scaledWeight w B start z*listReward (fun ps => |F ps|) z ∂pathLaw w ell ((Real.log B)^2) start n)
    exact hle.trans (by simpa using hn)
  rw [← finite_signed_original_occupation hw hell (sq_nonneg _) hS hr hs hsS hB hsize (fun ps => |F ps|)]
  calc
    _ ≤ ∑ _n ∈ range (NumberTheoryLean.LowStateHorizon.sourceHorizon ((Real.log B)^2) B),transferConstant*delta :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] <;> ring

end ErdosRetainedRewardTransfer

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceCenteredGap
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral Erdos970Dependency.InvariantCostBound
open NumberTheoryLean.PrimeHistories NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.JacobsthalSourceScale

theorem sourceRoot_eq_paper (a : ℝ) {z : ℝ} (hz : 1 < z) (hW : 1 < sourceW (Real.log z)) :
    sourceRootNode a z=paperStart a floorRemainder true (Real.log z) := by
  have hg := paperGap_floor_eq a (L := Real.log z) hW
  rw [Real.exp_log (by linarith : 0 < z)] at hg
  change paperGap a floorRemainder (Real.log z)=sourceRootGap a z at hg
  unfold sourceRootNode paperStart
  rw [hg]
  rfl

end ErdosCorrectionLimit

end

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
open ErdosCorrectionLimit
open NumberTheoryLean.JacobsthalSourceScale NumberTheoryLean.PrimeBinMembership

theorem rootW_tendsto : Tendsto ErdosInverseBoxHeight.sourceW atTop atTop := by
  exact sourceW_tendsto.comp Real.tendsto_log_atTop

theorem rootB_tendsto : Tendsto ErdosInverseBoxHeight.sourceB atTop atTop := by
  exact sourceB_tendsto.comp Real.tendsto_log_atTop

theorem actual_root_eventually (a : ℝ) : ∀ᶠ z : ℝ in atTop,
    0 < ErdosInverseBoxHeight.sourceB z ∧ 1 < ErdosInverseBoxHeight.sourceW z ∧
    Real.log (ErdosInverseBoxHeight.sourceB z) ≤ 2*Real.log (ErdosInverseBoxHeight.sourceW z) ∧
    199/100 ≤ (sourceRootNode a z).ratio ∧ (sourceRootNode a z).ratio ≤ 23/10 ∧
    0 < (sourceRootNode a z).gap ∧ Consistent (sourceRootNode a z) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (paper_start_eventually a true floorRemainder_tendsto),
    Real.tendsto_log_atTop.eventually source_scale_eventually,eventually_gt_atTop (1:ℝ)] with z hp hs hz
  simp only [sourceRoot_eq_paper a hz hs.1]
  exact hp

end ErdosSourceReferenceMargin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ResidualHistoryGeometry
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ResidualHistoryGeometry

attribute [local instance] Classical.propDecidable
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry ActualPrimeHigh ActualBoundaryDomain
open SourceNodeCoordinates ReferenceResidualSum ReferenceSourceDecomposition
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem uncapped_gap_le {w : ℝ} {z : Node} {ps : List ℕ} (hp : uncappedAllowed w 2 z ps) :
    (terminal w z ps).gap ≤ z.gap := by
  induction ps generalizing z with
  | nil => exact le_rfl
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hx : 2 < primeExponent w p := (Finset.mem_filter.mp hc).2.1
    calc
      _ ≤ (step w z p).gap := ih (z:=step w z p) ht
      _ ≤ z.gap := sub_le_self _ (by linarith)

theorem source_terminal_geometry {B w : ℝ} (hB : 4 ≤ B) (start : Node)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hc : Consistent start) (hcut : start.cutoff=B) {ps : List ℕ} (hp : uncappedAllowed w 2 start ps) :
    Valid (terminal w start ps).side (terminal w start ps).ratio ∧
    Consistent (terminal w start ps) ∧ BoundaryDomain (terminal w start ps).side (terminal w start ps).gap ∧
    2 < (terminal w start ps).cutoff ∧ (terminal w start ps).cutoff ≤ B ∧
    0 < (terminal w start ps).gap ∧ (terminal w start ps).gap ≤ (23/10:ℝ)*B := by
  obtain ⟨hs,hr,_hBstart,hsize⟩ := source_node_bounds (by linarith : 0 < B) start hi h199 h23 hc hcut
  obtain ⟨U,_hU,hpU⟩ := (uncapped_iff_exists_ceiling w 2 start ps).mp hp
  refine ⟨terminal_valid hs hpU,terminal_consistent (by norm_num) hr hs hc hpU,
    source_boundary_domain hB le_rfl start hi h199 h23 hc hcut hp,
    uncapped_cutoff_gt_two (by rw [hcut]; linarith) hp,?_,uncapped_gap_positive (by norm_num) hr hs hp,
    (uncapped_gap_le hp).trans hsize⟩
  simpa only [hcut] using uncapped_cutoff_le hp

end NumberTheoryLean.ResidualHistoryGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceReferenceRemainders
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.SharpRetainedResidual

attribute [local instance] Classical.propDecidable
open _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeKilledChain PrimeCorrectionFactor PrimeFamilyOccupation
open LowStateHorizon UniformBudgetRate ActualPrimeHigh SourceNodeCoordinates ResidualHistoryGeometry
open ReferenceLocalResidual ReferenceProductErrorBounds LowStateResidualBound
open ErdosPrimeInputs.PrimePrefixMass ErdosRetainedRewardTransfer

theorem retained_residual_sum_bound (d : ℝ) (hd : 0 < d) :
    ∃ c C B₀ w₀ : ℝ,0 < c ∧ 0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff=B →
      B^2*retainedResidualAbsoluteSum w B start ≤ C*((Real.log w)^16*primeError c w 2+1/B^4) := by
  obtain ⟨c,CP,T,wP,hc,hCP,hT,hwP,hP⟩ := low_state_normalized_residual_jb247 d hd
  obtain ⟨wBudget,hwBudget⟩ := eventually_atTop.mp
    ((correctionBudget_tendsto_zero d).eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)))
  let A := 5*transferConstant*CP
  have hA : 0 < A := by dsimp [A]; exact mul_pos (mul_pos (by norm_num) transferConstant_positive) hCP
  let C := A*(d^16+1)
  let B₀ := max 4 (Real.exp T)
  let w₀ := max wP (max normalizationThreshold (max wBudget (Real.exp (d^2))))
  refine ⟨c,C,B₀,w₀,hc,by dsimp [C] <;> positivity,by dsimp [B₀]; have hh := le_max_left (4:ℝ) (Real.exp T); linarith,
    hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hB4 : 4 ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := by linarith
  have hBexp : Real.exp T ≤ B := (le_max_right _ _).trans hB
  have hBT : T ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hBexp
  have hlogB : 2 ≤ Real.log B := hT.trans hBT
  have hL : 0 ≤ Real.log B := by linarith
  have hwP' : wP ≤ w := (le_max_left _ _).trans hw
  have hnorm : normalizationThreshold ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwBud : wBudget ≤ w := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hw
  have hwExp : Real.exp (d^2) ≤ w := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hw
  have hw1 : 1 < w := hwP.trans_le hwP'
  have hlogw : d^2 ≤ Real.log w := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hwExp
  have hS := (source_scale_bound hlogw hlogB hcomp).1
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hbudget := hwBudget w hwBud
  let delta := CP*((Real.log B)^13*primeError c w 2+1/B^7)
  have hE := primeError_pos c w 2
  have hdelta : 0 ≤ delta := by dsimp [delta] <;> positivity
  have hF : ∀ ps ∈ retainedPrefixes w 2 ((Real.log B)^2) start,
      (terminal w start ps).gap^2*|sourceResidual w (terminal w start ps)|/
        weight (terminal w start ps).side (terminal w start ps).ratio ≤ delta := by
    intro ps hp
    have hpA := (mem_retainedPrefixes hw1 start ps).mp hp
    have hpU : uncappedAllowed w 2 start ps :=
      (uncapped_iff_exists_ceiling w 2 start ps).mpr ⟨(Real.log B)^2,hsS,hpA⟩
    obtain ⟨hvs,hcs,hdom,hlo,hup,_hrp,hgup⟩ := source_terminal_geometry hB4 start hi h199 h23 hcons hcut hpU
    have hratio := terminal_ratio_le hsS hpA
    have hh := hP B w hBpos hBT hwP' hcomp _ hvs hcs hdom hlo.le hup hgup hratio
    calc
      _ = ((terminal w start ps).gap^2/weight (terminal w start ps).side (terminal w start ps).ratio)*
          |sourceResidual w (terminal w start ps)| := by ring
      _ ≤ delta := hh
  have hTransfer := retained_normalized_reward_sum (d:=d) (w:=w) (ell:=2) (B:=B) (delta:=delta) (start:=start)
    hnorm (by norm_num) hS hsS hBpos hlogB hcomp hbudget hi h199 h23 hcons hcut hdelta
    (fun ps => sourceResidual w (terminal w start ps)) hF
  have hN := source_horizon_log_cube hlogB
  have hraw : B^2*retainedResidualAbsoluteSum w B start ≤
      A*((Real.log B)^16*primeError c w 2+(Real.log B)^3/B^7) := by
    calc
      _ ≤ transferConstant*(sourceHorizon ((Real.log B)^2) B:ℝ)*delta := hTransfer
      _ ≤ transferConstant*(5*(Real.log B)^3)*delta :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN transferConstant_positive.le) hdelta
      _ = _ := by dsimp [A,delta] <;> ring
  have hlogw0 : 0 ≤ Real.log w := (Real.log_pos hw1).le
  have hpower : (Real.log B)^16 ≤ d^16*(Real.log w)^16 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hL hcomp 16
  have hlogB_le : Real.log B ≤ B := by linarith [Real.log_le_sub_one_of_pos hBpos]
  have hfrac : (Real.log B)^3/B^7 ≤ 1/B^4 := by
    calc
      _ ≤ B^3/B^7 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hL hlogB_le 3) (by positivity)
      _ = _ := by field_simp
  have hterm := mul_le_mul_of_nonneg_right hpower hE.le
  have hx : 0 ≤ (Real.log w)^16*primeError c w 2 := by positivity
  have hy : 0 ≤ (1:ℝ)/B^4 := by positivity
  calc
    _ ≤ A*((Real.log B)^16*primeError c w 2+(Real.log B)^3/B^7) := hraw
    _ ≤ A*(d^16*((Real.log w)^16*primeError c w 2)+1/B^4) := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      exact add_le_add (by simpa only [mul_assoc] using hterm) hfrac
    _ ≤ _ := by
      dsimp only [C]
      nlinarith only [mul_nonneg hA.le hx,mul_nonneg (mul_nonneg hA.le (pow_nonneg hd.le 16)) hy]

end NumberTheoryLean.SharpRetainedResidual



namespace NumberTheoryLean.SharpGlobalResidual

open _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeFamilyOccupation
open ReferenceLocalResidual ReferenceResidualSum ReferenceSourceDecomposition ReferenceLogScale
open SharpRetainedResidual HighResidualSum

theorem actual_residual_partition {w B : ℝ} (hw : 1 < w) {start : Node}
    (hsS : start.ratio ≤ (Real.log B)^2) :
    residualAbsoluteSum w start=retainedResidualAbsoluteSum w B start+highResidualAbsoluteSum w B start :=
  uncapped_sum_partition hw hsS (fun ps => ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps*|sourceResidual w (terminal w start ps)|)

theorem sharp_source_residual_sum (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → B^2*residualAbsoluteSum w start ≤ ε := by
  obtain ⟨c,CL,BL,wL,hc,hCL,hBL,hwL,hLow⟩ := retained_residual_sum_bound d hd
  obtain ⟨CH,BH,wH,hCH,_hBH,_hwH,hHigh⟩ := high_residual_sum_bound_jb247 d hd
  have hdec := log_power_primeError_tendsto CL 16 hc
  obtain ⟨wE,hwE⟩ := eventually_atTop.mp
    (hdec.eventually (eventually_le_nhds (show (0:ℝ)<ε/2 by linarith)))
  let B₀ := max BL (max BH (max (Real.exp 2) (2*(CL+CH)/ε)))
  let w₀ := max wL (max wH wE)
  refine ⟨B₀,w₀,hBL.trans_le (le_max_left _ _),hwL.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBL' : BL ≤ B := (le_max_left _ _).trans hB
  have hBH' : BH ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hBexp : Real.exp 2 ≤ B := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hB
  have hBlarge : 2*(CL+CH)/ε ≤ B := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hB
  have hBpos : 0 < B := hBL.trans_le hBL'
  have hlogB : 2 ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hB1 : 1 ≤ B := (Real.log_nonneg_iff hBpos).mp (by linarith)
  have hwL' : wL ≤ w := (le_max_left _ _).trans hw
  have hwH' : wH ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwE' : wE ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
  have hw1 : 1 < w := hwL.trans_le hwL'
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hlow := hLow B w hBL' hwL' hcomp start hi h199 h23 hcons hcut
  have hhigh := hHigh B w hBH' hwH' hcomp start hi h199 h23 hcons hcut
  have hB4 : B ≤ B^4 := by simpa only [pow_one] using pow_le_pow_right₀ hB1 (show (1:ℕ) ≤ 4 by norm_num)
  have hB6 : B ≤ B^6 := by simpa only [pow_one] using pow_le_pow_right₀ hB1 (show (1:ℕ) ≤ 6 by norm_num)
  have htail : CL/B^4+CH/B^6 ≤ ε/2 := by
    have hfrac : CL/B^4+CH/B^6 ≤ (CL+CH)/B := by
      calc
        _ ≤ CL/B+CH/B := add_le_add
          (div_le_div_of_nonneg_left hCL.le hBpos hB4) (div_le_div_of_nonneg_left hCH.le hBpos hB6)
        _ = _ := by ring
    apply hfrac.trans
    apply (div_le_iff₀ hBpos).mpr
    have hh := (div_le_iff₀ hε).mp hBlarge
    nlinarith
  have hsmall := hwE w hwE'
  rw [mul_add,mul_one_div] at hlow
  rw [actual_residual_partition hw1 hsS,mul_add]
  nlinarith only [hlow,hhigh,htail,hsmall]

theorem sharp_signed_residual (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → B^2*|residualCorrection w start| ≤ ε := by
  obtain ⟨B₀,w₀,hB₀,hw₀,h⟩ := sharp_source_residual_sum d ε hd hε
  refine ⟨B₀,w₀,hB₀,hw₀,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  exact (mul_le_mul_of_nonneg_left (signed_residual_le_absolute w start) (sq_nonneg B)).trans
    (h B w hB hw hcomp start hi h199 h23 hcons hcut)

end NumberTheoryLean.SharpGlobalResidual



namespace NumberTheoryLean.GlobalReferenceApproximation

open FinitePathGeometry PrimeHistories PrimeBinMembership SourceNodeCoordinates
open ReferenceLocalResidual ReferenceSourceDecomposition UniformBoundaryCorrection SharpGlobalResidual

theorem global_reference_remainder (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        B^2*|sourceReference w start-nodeBenchmark w start-boundaryCorrection w 2 start| ≤ ε := by
  obtain ⟨B₁,w₀,hB₁,hw₀,h⟩ := sharp_signed_residual d ε hd hε
  refine ⟨max B₁ 4,w₀,hB₁.trans_le (le_max_left _ _),hw₀,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hB₁' : B₁ ≤ B := (le_max_left _ _).trans hB
  have hB4 : 4 ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := by linarith
  obtain ⟨hs,hr,_h1,_h2⟩ := source_node_bounds hBpos start hi h199 h23 hcons hcut
  have he := actual_reference_decomposition (hw₀.trans_le hw) hs hr hcons (by rw [hcut]; linarith)
  have heq : sourceReference w start-nodeBenchmark w start-boundaryCorrection w 2 start=residualCorrection w start := by linarith
  rw [heq]
  exact h B w hB₁' hw hcomp start hi h199 h23 hcons hcut

end NumberTheoryLean.GlobalReferenceApproximation



open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
open ErdosCorrectionLimit ErdosContinuousAnomaly
open NumberTheoryLean.ReferenceSourceDecomposition NumberTheoryLean.ReferenceLocalResidual
open NumberTheoryLean.UniformBoundaryCorrection NumberTheoryLean.GlobalReferenceApproximation

theorem root_source_remainder_tendsto_jb247_oai (a : ℝ) :
    Tendsto (fun z => (ErdosInverseBoxHeight.sourceB z)^2*
      (sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode a z)-
        nodeBenchmark (ErdosInverseBoxHeight.sourceW z) (sourceRootNode a z)-
        boundaryCorrection (ErdosInverseBoxHeight.sourceW z) 2 (sourceRootNode a z))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨B₀,w₀,_hB₀,_hw₀,h⟩ := global_reference_remainder 2 (eps/2) (by norm_num) (by linarith)
  filter_upwards [actual_root_eventually a,rootB_tendsto.eventually (eventually_ge_atTop B₀),
    rootW_tendsto.eventually (eventually_ge_atTop w₀)] with z hs hB hw
  have hh := h (ErdosInverseBoxHeight.sourceB z) (ErdosInverseBoxHeight.sourceW z) hB hw hs.2.2.1
    (sourceRootNode a z) rfl hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.2 rfl
  rw [Real.dist_eq,sub_zero,abs_mul,abs_of_nonneg (sq_nonneg _)]
  exact hh.trans_lt (by linarith)

end ErdosSourceReferenceMargin


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosSourceReferenceMargin.root_source_remainder_tendsto_jb247_oai := @OAI.Erdos970.ErdosSourceReferenceMargin.root_source_remainder_tendsto_jb247_oai
