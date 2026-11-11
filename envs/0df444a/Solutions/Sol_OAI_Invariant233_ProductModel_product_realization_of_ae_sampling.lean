-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.product_realization_of_ae_sampling
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:21.054021+00:00
-- url     : https://prove2.me/submissions/77b0a175-7284-4811-a180-b7d55e34156d

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Countable
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Sequences
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_ProductModel_factor_complete
import Theorems.Thm_OAI_Invariant233_ProductModel_hasOnlyTrivialInvariantProjections_of_sampling_and_phases
import Theorems.Thm_OAI_Invariant233_ProductModel_productPolarStructure_of_admissible
import Theorems.Thm_OAI_Invariant233_ProductModel_weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral

section
-- module Solutions.Q234_IR.Compat
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `spectralRadius_eq_of_unital`: the spectral radius is the supremum of the norms over the spectrum. -/
theorem spectralRadius_eq_of_unital {𝕜 A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A] (a : A) :
    spectralRadius 𝕜 a = ⨆ k ∈ spectrum 𝕜 a, (‖k‖₊ : ENNReal) := rfl
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockReciprocalSum
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace InvariantProjection.IndependentAngles

theorem tsum_fin_block_reciprocal {m : ℕ} (hm : 0 < m) (K : ℝ) :
    (∑' _i : Fin m, 1 / ((m : ℝ) * K)) = 1 / K := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  by_cases hK : K = 0
  · simp [hK]
  · field_simp

theorem summable_block_reciprocal (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hsum : Summable (fun j => 1 / K j)) :
    Summable (fun i : Σ j, Fin (m j) => 1 / ((m i.1 : ℝ) * K i.1)) := by
  apply (summable_sigma_of_nonneg (fun i => div_nonneg (by norm_num)
    (mul_nonneg (Nat.cast_nonneg _) (hK i.1).le))).2
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fin_block_reciprocal (hm _) (K _)] using hsum

theorem tsum_block_reciprocal (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hsum : Summable (fun j => 1 / K j)) :
    (∑' i : Σ j, Fin (m j), 1 / ((m i.1 : ℝ) * K i.1)) = ∑' j, 1 / K j := by
  rw [(summable_block_reciprocal m hm K hK hsum).tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fin_block_reciprocal (hm _) (K _)]

theorem enumerated_block_reciprocal {ι : Type*} (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hsum : Summable (fun j => 1 / K j)) (e : ι ≃ Σ j, Fin (m j)) :
    Summable (fun i => 1 / ((m (e i).1 : ℝ) * K (e i).1)) ∧
    (∑' i, 1 / ((m (e i).1 : ℝ) * K (e i).1)) = ∑' j, 1 / K j := by
  constructor
  · exact e.summable_iff.mpr (summable_block_reciprocal m hm K hK hsum)
  · calc
      (∑' i, 1 / ((m (e i).1 : ℝ) * K (e i).1)) =
          ∑' i : Σ j, Fin (m j), 1 / ((m i.1 : ℝ) * K i.1) := e.tsum_eq (fun i : Σ j, Fin (m j) => 1 / ((m i.1 : ℝ) * K i.1))
      _ = ∑' j, 1 / K j := tsum_block_reciprocal m hm K hK hsum

end InvariantProjection.IndependentAngles

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConsecutiveBlocks
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace InvariantProjection.IndependentAngles

theorem consecutiveBlocks_bijective (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) :
    Function.Bijective
      (fun i : Σ j, Fin (m j) => (∑ r ∈ Finset.range i.1, m r) + i.2.val) := by
  let d : ℕ → ℕ := fun j => ∑ r ∈ Finset.range j, m r
  have hd0 : d 0 = 0 := by simp [d]
  have hstep : ∀ j, d (j + 1) = d j + m j := fun j => Finset.sum_range_succ m j
  have hmono : Monotone d := fun j k hjk =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hjk)
  have hlarge : ∀ j, j ≤ d j := by
    intro j
    induction j with
    | zero => omega
    | succ j hj =>
        have hp := hm j
        rw [hstep]
        omega
  have hgap : ∀ {j k}, j < k → d j + m j ≤ d k := by
    intro j k hjk
    rw [← hstep]
    exact hmono (by omega)
  constructor
  · rintro ⟨j, u⟩ ⟨k, v⟩ heq
    change d j + u.val = d k + v.val at heq
    have hjk : j = k := by
      rcases lt_trichotomy j k with h | h | h
      · have hg := hgap h
        have hu := u.isLt
        omega
      · exact h
      · have hg := hgap h
        have hv := v.isLt
        omega
    subst k
    have huv : u = v := Fin.ext (by omega)
    subst v
    rfl
  · intro n
    have hex : ∃ j, n < d (j + 1) := ⟨n, by have := hlarge (n + 1); omega⟩
    let j := Nat.find hex
    have hupper : n < d (j + 1) := Nat.find_spec hex
    have hlower : d j ≤ n := by
      by_cases hj : j = 0
      · simp [hj, hd0]
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hn : ¬n < d (j - 1 + 1) := Nat.find_min hex (by change j - 1 < j; omega)
        have hpred : j - 1 + 1 = j := by omega
        rw [hpred] at hn
        omega
    have hi : n - d j < m j := by
      rw [hstep] at hupper
      omega
    refine ⟨⟨j, ⟨n - d j, hi⟩⟩, ?_⟩
    change d j + (n - d j) = n
    omega

theorem exists_consecutiveBlocks_equiv (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) :
    ∃ e : ℕ ≃ Σ j, Fin (m j), ∀ i : Σ j, Fin (m j),
      e.symm i = (∑ r ∈ Finset.range i.1, m r) + i.2.val := by
  let e : (Σ j, Fin (m j)) ≃ ℕ :=
    Equiv.ofBijective _ (consecutiveBlocks_bijective m hm)
  exact ⟨e.symm, fun _ => rfl⟩

end InvariantProjection.IndependentAngles

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ExponentialDecay
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
open scoped BigOperators ENNReal

namespace Invariant233

theorem spectralRadius_zero_of_norm_root_tendsto_zero {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (T : A)
    (hroot : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    spectralRadius ℂ T = 0 := by
  have hzero : Tendsto
      (fun n : ℕ => ENNReal.ofReal (‖T ^ n‖ ^ (1 / (n : ℝ))))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hroot
  exact tendsto_nhds_unique
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius T) hzero

theorem spectrum_subset_zero_of_spectralRadius_zero {𝕜 A : Type*}
    [NormedField 𝕜] [Ring A] [Algebra 𝕜 A] (T : A)
    (hzero : spectralRadius 𝕜 T = 0) :
    spectrum 𝕜 T ⊆ {0} := by
  intro z hz
  have hnorm : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius 𝕜 T := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun scalar (_ : scalar ∈ spectrum 𝕜 T) =>
      (‖scalar‖₊ : ℝ≥0∞)) z hz
  rw [hzero] at hnorm
  simpa using hnorm

theorem spectrum_eq_zero_of_spectralRadius_zero {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (T : A)
    (hzero : spectralRadius ℂ T = 0) : spectrum ℂ T = {0} := by
  have hsub := spectrum_subset_zero_of_spectralRadius_zero T hzero
  apply Set.Subset.antisymm hsub
  obtain ⟨z, hz⟩ := spectrum.nonempty T
  have hz0 : z = 0 := hsub hz
  simpa only [Set.singleton_subset_iff, hz0] using hz

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ExtendedExponential
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.negLogCost_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal

namespace Invariant233

theorem negLogCost_extendedExpNeg (a : ℝ≥0∞) :
    negLogCost ((EReal.exp (-(a : EReal))).toReal) = a := by
  by_cases ha : a = ∞
  · simp [ha, negLogCost]
  · rw [extendedExpNeg_eq_exp_toReal a ha]
    simp only [negLogCost, Real.exp_ne_zero, ite_false, if_false,
      abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg]
    exact ENNReal.ofReal_toReal ha

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_InvariantConullCore
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233

theorem exists_invariant_conull_subset
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    {s : Set X} (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧
      (∀ᵐ x ∂μ, x ∈ t) ∧ ∀ k, σ k ⁻¹' t = t := by
  let t : Set X := ⋂ k : ℤ, σ k ⁻¹' s
  have ht_mem : ∀ x, x ∈ t ↔ ∀ k, σ k x ∈ s := by
    intro x
    simp only [t, mem_iInter, mem_preimage]
  refine ⟨t, MeasurableSet.iInter (fun k ↦ hs.preimage (hmp k).measurable), ?_, ?_, ?_⟩
  · intro x hx
    simpa only [hzero] using (ht_mem x).mp hx 0
  · have h : ∀ᵐ x ∂μ, ∀ k : ℤ, σ k x ∈ s :=
      ae_all_iff.mpr (fun k ↦ (hmp k).quasiMeasurePreserving.ae hfull)
    exact h.mono fun x hx ↦ (ht_mem x).mpr hx
  · intro k
    ext x
    change σ k x ∈ t ↔ x ∈ t
    rw [ht_mem, ht_mem]
    constructor
    · intro hx n
      have h := hx (n - k)
      rw [← hadd] at h
      rw [← add_sub_assoc, add_comm k n, add_sub_cancel_right] at h
      exact h
    · intro hx n
      rw [← hadd]
      exact hx (k + n)

theorem exists_invariant_conull_property
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    (P : X → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ t) ∧
      (∀ x ∈ t, P x) ∧ ∀ k, σ k ⁻¹' t = t := by
  obtain ⟨u, hsub, hu, hnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hP)
  have hfull : ∀ᵐ x ∂μ, x ∈ uᶜ := by
    rw [ae_iff]
    simpa using hnull
  obtain ⟨t, ht, htu, htf, hinv⟩ :=
    exists_invariant_conull_subset σ hzero hadd hmp hu.compl hfull
  refine ⟨t, ht, htf, ?_, hinv⟩
  intro x hx
  by_contra hbad
  exact htu hx (hsub hbad)

theorem exists_invariant_conull_forall
    {X I : Type*} [MeasurableSpace X] [Countable I] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    (P : I → X → Prop) (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ t) ∧
      (∀ x ∈ t, ∀ k i, P i (σ k x)) ∧ ∀ k, σ k ⁻¹' t = t := by
  obtain ⟨t, ht, htf, hprop, hinv⟩ :=
    exists_invariant_conull_property σ hzero hadd hmp
      (fun x ↦ ∀ i, P i x) (ae_all_iff.mpr hP)
  refine ⟨t, ht, htf, ?_, hinv⟩
  intro x hx k i
  apply hprop (σ k x) _ i
  change x ∈ σ k ⁻¹' t
  rw [hinv]
  exact hx

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ModuloIntervalMeasure
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ModuloIntervalMeasure

open Set MeasureTheory
open scoped ENNReal

theorem integral_periodic_le_length_add_one {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hf : ∀ x, 0 ≤ f x)
    (hint : IntervalIntegrable f volume 0 1) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x) ≤ (b - a + 1) * ∫ x in (0 : ℝ)..1, f x := by
  let n : ℕ := ⌈b - a⌉₊
  have hn : b ≤ a + n := by
    have := Nat.le_ceil (b - a)
    dsimp [n]
    linarith
  have hn' : (n : ℝ) ≤ b - a + 1 := by
    exact (Nat.ceil_lt_add_one (sub_nonneg.mpr hab)).le
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have hmass : 0 ≤ ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) hf
  calc
    (∫ x in a..b, f x) ≤ ∫ x in a..a + n, f x :=
      intervalIntegral.integral_mono_interval le_rfl hab hn
        (Filter.Eventually.of_forall hf) (hint' _ _)
    _ = (n : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
      have h := hperiod.intervalIntegral_add_zsmul_eq (n : ℤ) a hint'
      simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one,
        hperiod.intervalIntegral_add_eq a 0, zero_add] using h
    _ ≤ (b - a + 1) * ∫ x in (0 : ℝ)..1, f x :=
      mul_le_mul_of_nonneg_right hn' hmass

theorem periodic_fract_indicator (s : Set ℝ) :
    Function.Periodic ((Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ))) 1 := by
  classical
  intro x
  change (if Int.fract (x + 1) ∈ s then (1 : ℝ) else 0) =
    (if Int.fract x ∈ s then 1 else 0)
  rw [Int.fract_add_one]

theorem intervalIntegrable_indicator_one {s : Set ℝ} (hs : MeasurableSet s)
    (a b : ℝ) : IntervalIntegrable (s.indicator (fun _ => (1 : ℝ))) volume a b := by
  exact ⟨(integrable_const (1 : ℝ)).indicator hs,
    (integrable_const (1 : ℝ)).indicator hs⟩

theorem integral_fract_indicator_one_period {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ x in (0 : ℝ)..1, (Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ)) x) =
      volume.real (s ∩ Ico 0 1) := by
  calc
    (∫ x in (0 : ℝ)..1, (Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ)) x) =
        ∫ x in (0 : ℝ)..1, s.indicator (fun _ => (1 : ℝ)) x := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      classical
      intro x hx
      have hfract := Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩
      change (if Int.fract x ∈ s then (1 : ℝ) else 0) =
        (if x ∈ s then 1 else 0)
      rw [hfract]
    _ = volume.real (s ∩ Ico 0 1) := by
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc,
        integral_indicator_const 1 hs, measureReal_restrict_apply hs]
      simp

theorem volume_fract_preimage_inter_Ioc_le {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hab : a ≤ b) :
    volume.real (Int.fract ⁻¹' s ∩ Ioc a b) ≤
      (b - a + 1) * volume.real (s ∩ Ico 0 1) := by
  have hs' : MeasurableSet (Int.fract ⁻¹' s) := hs.preimage measurable_fract
  have hnonneg : ∀ x, 0 ≤ (Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have h := integral_periodic_le_length_add_one (periodic_fract_indicator s) hnonneg
    (intervalIntegrable_indicator_one hs' 0 1) hab
  rw [integral_fract_indicator_one_period hs, intervalIntegral.integral_of_le hab,
    integral_indicator_const 1 hs', measureReal_restrict_apply hs'] at h
  simpa only [smul_eq_mul, mul_one] using h

theorem cond_fract_preimage_le {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hab : a < b) :
    (ProbabilityTheory.cond volume (Ioc a b)).real (Int.fract ⁻¹' s) ≤
      (1 + 1 / (b - a)) * volume.real (s ∩ Ico 0 1) := by
  have hr : 0 < b - a := sub_pos.mpr hab
  have h := mul_le_mul_of_nonneg_left
    (volume_fract_preimage_inter_Ioc_le hs hab.le) (inv_nonneg.mpr hr.le)
  rw [ProbabilityTheory.cond, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply (hs.preimage measurable_fract),
    ENNReal.toReal_inv, Real.volume_Ioc, ENNReal.toReal_ofReal hr.le]
  calc
    _ ≤ (b - a)⁻¹ * ((b - a + 1) * volume.real (s ∩ Ico 0 1)) := h
    _ = (1 + 1 / (b - a)) * volume.real (s ∩ Ico 0 1) := by
      rw [← mul_assoc, mul_add, inv_mul_cancel₀ hr.ne', mul_one, one_div]

theorem threshold_miss_unit_volume_le {w : ℝ} (hw : 0 ≤ w) :
    volume.real ({u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1) ≤ 2 * w := by
  have hsub : {u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1 ⊆
      Ico 0 w ∪ Ioo (1 - w) 1 := by
    intro u hu
    rcases hu with ⟨hbad, hu0, hu1⟩
    by_cases huw : u < w
    · exact Or.inl ⟨hu0, huw⟩
    · right
      refine ⟨?_, hu1⟩
      by_contra h
      apply hbad
      constructor <;> linarith
  calc
    volume.real ({u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1) ≤
        volume.real (Ico 0 w ∪ Ioo (1 - w) 1) := measureReal_mono hsub (measure_union_lt_top
          (by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top)
          (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)).ne
    _ ≤ volume.real (Ico 0 w) + volume.real (Ioo (1 - w) 1) :=
      measureReal_union_le _ _
    _ = 2 * w := by
      rw [Real.volume_real_Ico_of_le hw, Real.volume_real_Ioo_of_le (by linarith)]
      ring

theorem cond_threshold_miss_le {a b w : ℝ} (hlen : (1 : ℝ) / 4 ≤ b - a)
    (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Ioc a b)).real
      {t : ℝ | 1 - Int.fract t ∉ Icc w (1 - w)} ≤ 10 * w := by
  have hab : a < b := by linarith
  have hs : MeasurableSet {u : ℝ | 1 - u ∉ Icc w (1 - w)} :=
    (measurableSet_Icc.preimage (measurable_const.sub measurable_id)).compl
  have h := cond_fract_preimage_le hs hab
  have hr : 0 < b - a := sub_pos.mpr hab
  have hfactor : 1 + 1 / (b - a) ≤ 5 := by
    have : 1 / (b - a) ≤ 4 := (div_le_iff₀ hr).mpr (by linarith)
    linarith
  change (ProbabilityTheory.cond volume (Ioc a b)).real (Int.fract ⁻¹'
    {u : ℝ | 1 - u ∉ Icc w (1 - w)}) ≤ 10 * w
  calc
    _ ≤ (1 + 1 / (b - a)) * volume.real
        ({u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1) := h
    _ ≤ 5 * (2 * w) := mul_le_mul hfactor (threshold_miss_unit_volume_le hw)
      measureReal_nonneg (by norm_num)
    _ = 10 * w := by ring

theorem cond_Icc_eq_cond_Ioc (a b : ℝ) :
    ProbabilityTheory.cond volume (Icc a b) = ProbabilityTheory.cond volume (Ioc a b) := by
  simp only [ProbabilityTheory.cond, Real.volume_Icc, Real.volume_Ioc]
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume)).symm]

theorem cond_uIcc_mul_preimage (a b k : ℝ) (hk : k ≠ 0) (s : Set ℝ) :
    (ProbabilityTheory.cond volume (uIcc a b)).real ((k * ·) ⁻¹' s) =
      (ProbabilityTheory.cond volume (uIcc (k * a) (k * b))).real s := by
  have hpre : (k * ·) ⁻¹' uIcc (k * a) (k * b) = uIcc a b := by
    rw [preimage_const_mul_uIcc hk]
    field_simp
  have hbase : volume (uIcc a b) =
      ENNReal.ofReal |k⁻¹| * volume (uIcc (k * a) (k * b)) := by
    rw [← hpre, Real.volume_preimage_mul_left hk]
  have hinter : volume (uIcc a b ∩ (k * ·) ⁻¹' s) =
      ENNReal.ofReal |k⁻¹| * volume (uIcc (k * a) (k * b) ∩ s) := by
    rw [← hpre, ← preimage_inter, Real.volume_preimage_mul_left hk]
  simp only [measureReal_def, ProbabilityTheory.cond_apply measurableSet_uIcc,
    hbase, hinter, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (abs_nonneg k⁻¹), mul_inv_rev]
  have hscale : |k⁻¹| ≠ 0 := abs_ne_zero.mpr (inv_ne_zero hk)
  rw [mul_assoc, ← mul_assoc |k⁻¹|⁻¹, inv_mul_cancel₀ hscale, one_mul]

theorem cond_uIcc_threshold_miss_le {a b w : ℝ}
    (hlen : (1 : ℝ) / 4 ≤ |b - a|) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (uIcc a b)).real
      {t : ℝ | 1 - Int.fract t ∉ Icc w (1 - w)} ≤ 10 * w := by
  rw [uIcc, cond_Icc_eq_cond_Ioc]
  apply cond_threshold_miss_le _ hw
  simpa only [max_sub_min_eq_abs] using hlen

theorem uniform_angle_threshold_miss_le {N k w : ℝ} (hN : 0 < N)
    (hk : N / 4 ≤ |k|) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Icc (1 / N) (2 / N))).real
      {θ : ℝ | 1 - Int.fract (k * θ) ∉ Icc w (1 - w)} ≤ 10 * w := by
  have hk0 : k ≠ 0 := by
    intro h
    simp only [h, abs_zero] at hk
    linarith
  have hab : (1 : ℝ) / N ≤ 2 / N := by
    apply div_le_div_of_nonneg_right (by norm_num) hN.le
  rw [← uIcc_of_le hab]
  change (ProbabilityTheory.cond volume (uIcc (1 / N) (2 / N))).real
    ((k * ·) ⁻¹' {t : ℝ | 1 - Int.fract t ∉ Icc w (1 - w)}) ≤ 10 * w
  rw [cond_uIcc_mul_preimage _ _ _ hk0]
  apply cond_uIcc_threshold_miss_le _ hw
  have hlength : |k * (2 / N) - k * (1 / N)| = |k| / N := by
    rw [← mul_sub, ← sub_div, show (2 : ℝ) - 1 = 1 by norm_num,
      mul_one_div, abs_div, abs_of_pos hN]
  rw [hlength]
  exact (le_div_iff₀ hN).mpr (by linarith)

end Invariant233.ModuloIntervalMeasure

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TruncatedLogIntegral
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lintegral_cost_eq_iSup_truncations (g : X → ℝ) (hm : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂μ) =
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ := by
  have hsup (x : X) :
      (⨆ n : ℕ, ENNReal.ofReal (min (g x) (n : ℝ))) = ENNReal.ofReal (g x) := by
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · obtain ⟨n, hn⟩ := exists_nat_gt (g x)
      exact le_iSup_of_le n (by rw [min_eq_left hn.le])
  rw [← lintegral_iSup]
  · exact lintegral_congr (fun x => (hsup x).symm)
  · intro n
    exact (hm.min measurable_const).ennreal_ofReal
  · intro n m hnm x
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hnm))

theorem integrable_min_nat_cost [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x) (n : ℕ) :
    Integrable (fun x => min (g x) (n : ℝ)) μ := by
  refine (integrable_const (μ := μ) (n : ℝ)).mono'
    (hm.min measurable_const).aestronglyMeasurable ?_
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hg x) (Nat.cast_nonneg n))]
    exact min_le_right _ _

theorem exists_integral_truncation_gt [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hinf : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) (A : ℝ) :
    ∃ n : ℕ, A < ∫ x, min (g x) (n : ℝ) ∂μ := by
  have hs : (⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ) = ∞ := by
    rw [← lintegral_cost_eq_iSup_truncations g hm, hinf]
  have ht : ENNReal.ofReal A <
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ := by
    rw [hs]
    exact ENNReal.ofReal_lt_top
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp ht
  refine ⟨n, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_min_nat_cost g hm hg n)
    (ae_of_all μ fun x => le_min (hg x) (Nat.cast_nonneg n))] at hn
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hn).1

theorem log_max_exp_neg (g M : ℝ) :
    Real.log (max (Real.exp (-g)) (Real.exp (-M))) = -min g M := by
  rcases le_total g M with h | h
  · rw [max_eq_left (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp, min_eq_left h]
  · rw [max_eq_right (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp, min_eq_right h]

theorem integral_truncated_log_eq_neg_cost
    (f g : X → ℝ) (hfg : f =ᵐ[μ] fun x => Real.exp (-g x)) (M : ℝ) :
    (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) =
      -(∫ x, min (g x) M ∂μ) := by
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx, log_max_exp_neg]

theorem tendsto_integral_truncations_atTop [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hinf : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) :
    Tendsto (fun n : ℕ => ∫ x, min (g x) (n : ℝ) ∂μ) atTop atTop := by
  apply tendsto_atTop.2
  intro A
  obtain ⟨n, hn⟩ := exists_integral_truncation_gt g hm hg hinf A
  filter_upwards [eventually_ge_atTop n] with m hnm
  refine hn.le.trans (integral_mono (integrable_min_nat_cost g hm hg n)
    (integrable_min_nat_cost g hm hg m) ?_)
  intro x
  exact min_le_min (le_refl (g x)) (Nat.cast_le.mpr hnm)

theorem tendsto_truncated_log_integrals_atBot [IsFiniteMeasure μ]
    (f : X → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) :
    Tendsto (fun n : ℕ => ∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ)
      atTop atBot := by
  have hfg : f =ᵐ[μ] fun x => Real.exp (-(-Real.log (f x))) := by
    filter_upwards [hpos] with x hx
    simp [Real.exp_log hx]
  have h := tendsto_neg_atTop_atBot.comp
    (tendsto_integral_truncations_atTop (fun x => -Real.log (f x)) hm.log.neg
      (fun x => neg_nonneg.mpr (Real.log_nonpos (hf0 x) (hf1 x))) hinf)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact integral_truncated_log_eq_neg_cost f (fun x => -Real.log (f x)) hfg (n : ℝ)

theorem exists_pos_truncated_log_integral_lt [IsFiniteMeasure μ]
    (f : X → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) (a : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) < -2 * a := by
  have hlim := tendsto_truncated_log_integrals_atBot f hm hf0 hf1 hpos hinf
  have hneg : ∀ᶠ n : ℕ in atTop,
      (∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ) < -2 * a :=
    hlim.eventually (eventually_lt_atBot (-2 * a))
  obtain ⟨n, hn, hnint⟩ := ((eventually_gt_atTop (0 : ℕ)).and hneg).exists
  exact ⟨n, Nat.cast_pos.mpr hn, hnint⟩

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentAngles
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace InvariantProjection.IndependentAngles

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_add_ne_of_indep [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ)
    [NullSingletonClass (μ.map Y)] (c : ℝ) :
    ∀ᵐ ω ∂μ, X ω + Y ω ≠ c := by
  have hset : MeasurableSet {z : ℝ × ℝ | z.1 + z.2 ≠ c} := by
    exact (measurable_fst.add measurable_snd) (measurableSet_singleton c).compl
  have hp : ∀ᵐ z ∂(μ.map X).prod (μ.map Y), z.1 + z.2 ≠ c := by
    apply (ae_prod_iff_ae_ae hset).2
    exact Filter.Eventually.of_forall fun x =>
      ((μ.map Y).ae_ne (c - x)).mono fun y hy h => hy (by linarith)
  rw [← hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable] at hp
  exact ae_of_ae_map (hX.prodMk hY).aemeasurable hp

theorem nullSingletonClass_map_mul {X : Ω → ℝ} (hX : Measurable X)
    [NullSingletonClass (μ.map X)] {c : ℝ} (hc : c ≠ 0) :
    NullSingletonClass (μ.map (fun ω => c * X ω)) := by
  constructor
  intro y
  rw [Measure.map_apply (show Measurable (fun ω => c * X ω) from
    measurable_const.mul hX) (measurableSet_singleton y)]
  have hsub : (fun ω => c * X ω) ⁻¹' {y} ⊆ X ⁻¹' {y / c} := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    apply (eq_div_iff hc).2
    simpa [mul_comm] using hω
  apply measure_mono_null hsub
  rw [← Measure.map_apply hX (measurableSet_singleton (y / c))]
  exact measure_singleton _

theorem ae_finset_sum_ne [IsProbabilityMeasure μ] [DecidableEq ι]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i)))
    (s : Finset ι) (c : ι → ℝ) {i : ι} (hi : i ∈ s) (hci : c i ≠ 0)
    (r : ℝ) : ∀ᵐ ω ∂μ, (∑ j ∈ s, c j * X j ω) ≠ r := by
  let Y : ι → Ω → ℝ := fun j ω => c j * X j ω
  have hY : ∀ j, Measurable (Y j) := fun j => measurable_const.mul (hX j)
  have hindY : iIndepFun Y μ := hind.comp (fun j x => c j * x)
    (fun _ => measurable_const.mul measurable_id)
  have hsumInd : IndepFun (∑ j ∈ s.erase i, Y j) (Y i) μ :=
    hindY.indepFun_finsetSum_of_notMem hY (Finset.notMem_erase i s)
  let : NullSingletonClass (μ.map (X i)) := hno i
  let : NullSingletonClass (μ.map (Y i)) :=
    nullSingletonClass_map_mul (hX i) hci
  have hsum : Measurable (∑ j ∈ s.erase i, Y j) := by
    change Measurable (fun ω => (∑ j ∈ s.erase i, Y j) ω)
    simp only [Finset.sum_apply]
    exact Finset.measurable_sum (s.erase i) (fun j _ => hY j)
  filter_upwards [ae_add_ne_of_indep hsum (hY i) hsumInd r] with ω hω
  convert hω using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Finset.sum_apply, Y]
  exact (Finset.sum_erase_add _ _ hi).symm

theorem ae_finsupp_sum_ne [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i)))
    (c : ι →₀ ℚ) (hc : c ≠ 0) (r : ℝ) :
    ∀ᵐ ω ∂μ, c.sum (fun j q => (q : ℝ) * X j ω) ≠ r := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hci : (c i : ℝ) ≠ 0 := by
    exact_mod_cast Finsupp.mem_support_iff.mp hi
  exact ae_finset_sum_ne hX hind hno c.support (fun j => (c j : ℝ)) hi hci r

theorem ae_no_rational_affine_relation [Countable ι] [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i))) :
    ∀ᵐ ω ∂μ, ∀ (c : ι →₀ ℚ) (q : ℚ),
      (q : ℝ) + c.sum (fun j r => (r : ℝ) * X j ω) = 0 → c = 0 ∧ q = 0 := by
  apply ae_all_iff.mpr
  intro c
  apply ae_all_iff.mpr
  intro q
  by_cases hc : c = 0
  · subst c
    exact Filter.Eventually.of_forall fun ω h => ⟨rfl, by simpa using h⟩
  · filter_upwards [ae_finsupp_sum_ne hX hind hno c hc (-(q : ℝ))] with ω hω
    intro heq
    exact False.elim (hω (by linarith))

theorem ae_linearIndependent_with_one [Countable ι] [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i))) :
    ∀ᵐ ω ∂μ, LinearIndependent ℚ (fun o : Option ι => o.elim 1 (fun i => X i ω)) := by
  filter_upwards [ae_no_rational_affine_relation hX hind hno] with ω hω
  rw [linearIndependent_iff]
  intro l hl
  rw [Finsupp.linearCombination_apply, Finsupp.sum_option_index_smul] at hl
  have hrel : (l none : ℝ) + l.some.sum (fun j r => (r : ℝ) * X j ω) = 0 := by
    simpa only [Option.elim_none, Option.elim_some, Rat.smul_def, mul_one] using hl
  obtain ⟨hsome, hnone⟩ := hω l.some (l none) hrel
  ext o
  cases o with
  | none => exact hnone
  | some i =>
      change l.some i = 0
      rw [hsome]
      rfl

theorem infinitePi_ae_linearIndependent_with_one [Countable ι]
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, NullSingletonClass (ν i)] :
    ∀ᵐ θ ∂Measure.infinitePi ν,
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) := by
  have hm : ∀ i : ι, Measurable (fun θ : ι → ℝ => θ i) :=
    fun i => measurable_pi_apply i
  have hi : iIndepFun (fun i (θ : ι → ℝ) => θ i) (Measure.infinitePi ν) :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have hn : ∀ i : ι, NullSingletonClass
      ((Measure.infinitePi ν).map (fun θ : ι → ℝ => θ i)) := by
    intro i
    rw [Measure.infinitePi_map_eval]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact ae_linearIndependent_with_one hm hi hn

theorem intervalLaw_isProbabilityMeasure {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc a b)) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

theorem intervalLaw_nullSingletonClass (a b : ℝ) :
    NullSingletonClass (ProbabilityTheory.cond volume (Set.Icc a b)) := by
  constructor
  intro x
  exact ProbabilityTheory.cond_absolutelyContinuous (measure_singleton x)

theorem intervalProduct_ae_bounds_linearIndependent [Countable ι]
    (a b : ι → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume (Set.Icc (a i) (b i))),
      (∀ i, θ i ∈ Set.Icc (a i) (b i)) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) := by
  let ν : ι → Measure ℝ := fun i => ProbabilityTheory.cond volume (Set.Icc (a i) (b i))
  let (i : ι) : IsProbabilityMeasure (ν i) := intervalLaw_isProbabilityMeasure (hab i)
  let (i : ι) : NullSingletonClass (ν i) := intervalLaw_nullSingletonClass (a i) (b i)
  have hb : ∀ᵐ θ ∂Measure.infinitePi ν, ∀ i, θ i ∈ Set.Icc (a i) (b i) := by
    apply ae_all_iff.mpr
    intro i
    have hi : ∀ᵐ x ∂(Measure.infinitePi ν).map (fun θ => θ i),
        x ∈ Set.Icc (a i) (b i) := by
      rw [Measure.infinitePi_map_eval]
      exact ae_cond_mem measurableSet_Icc
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hi
  exact hb.and (infinitePi_ae_linearIndependent_with_one ν)

theorem prescribedIntervals_ae_summable_independent [Countable ι]
    (N : ι → ℝ) (hN : ∀ i, 0 < N i) (hsum : Summable (fun i => 1 / N i)) :
    ∀ᵐ θ ∂Measure.infinitePi
        (fun i => ProbabilityTheory.cond volume (Set.Icc (1 / N i) (2 / N i))),
      (∀ i, θ i ∈ Set.Icc (1 / N i) (2 / N i)) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' i, 1 / N i) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) := by
  have hinterval : ∀ i, (1 : ℝ) / N i < 2 / N i := fun i =>
    div_lt_div_of_pos_right (by norm_num) (hN i)
  filter_upwards [intervalProduct_ae_bounds_linearIndependent
    (fun i => 1 / N i) (fun i => 2 / N i) hinterval] with θ hθ
  have hnonneg : ∀ i, 0 ≤ θ i := fun i =>
    (le_of_lt (one_div_pos.mpr (hN i))).trans (hθ.1 i).1
  have hupper : ∀ i, θ i ≤ 2 * (1 / N i) := by
    intro i
    simpa only [mul_one_div] using (hθ.1 i).2
  have hsumθ : Summable θ :=
    Summable.of_nonneg_of_le hnonneg hupper (hsum.mul_left 2)
  refine ⟨hθ.1, hsumθ, ?_, hθ.2⟩
  calc
    (∑' i, θ i) ≤ ∑' i, 2 * (1 / N i) :=
      hsumθ.tsum_le_tsum hupper (hsum.mul_left 2)
    _ = 2 * (∑' i, 1 / N i) := tsum_mul_left

theorem exists_prescribed_summable_independent_and [Countable ι]
    (N : ι → ℝ) (hN : ∀ i, 0 < N i) (hsum : Summable (fun i => 1 / N i))
    {P : (ι → ℝ) → Prop}
    (hP : ∀ᵐ θ ∂Measure.infinitePi
      (fun i => ProbabilityTheory.cond volume (Set.Icc (1 / N i) (2 / N i))), P θ) :
    ∃ θ : ι → ℝ, (∀ i, θ i ∈ Set.Icc (1 / N i) (2 / N i)) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' i, 1 / N i) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) ∧ P θ := by
  let (i : ι) : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N i) (2 / N i))) :=
    intervalLaw_isProbabilityMeasure (div_lt_div_of_pos_right (by norm_num) (hN i))
  obtain ⟨θ, hθ, hp⟩ :=
    ((prescribedIntervals_ae_summable_independent N hN hsum).and hP).exists
  exact ⟨θ, hθ.1, hθ.2.1, hθ.2.2.1, hθ.2.2.2, hp⟩

end InvariantProjection.IndependentAngles

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentMissBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem measure_many_independent_events_le
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : ι → Set Ω) (hE : iIndepSet E μ) (s : Finset ι)
    {p : ℝ≥0∞} (hp : p ≤ 1) (hprob : ∀ i ∈ s, μ (E i) ≤ p) (q : ℝ) :
    μ {ω | ∃ t : Finset ι, t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E i} ≤
      (2 : ℝ≥0∞) ^ s.card * p ^ q := by
  classical
  let F := s.powerset.filter (fun t => q ≤ (t.card : ℝ))
  have hset : {ω | ∃ t : Finset ι, t ⊆ s ∧ q ≤ (t.card : ℝ) ∧
      ∀ i ∈ t, ω ∈ E i} = ⋃ t ∈ F, ⋂ i ∈ t, E i := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, F,
      Finset.mem_filter, Finset.mem_powerset]
    aesop
  have hFcard : F.card ≤ 2 ^ s.card := by
    calc
      F.card ≤ s.powerset.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ s.card := Finset.card_powerset s
  rw [hset]
  calc
    μ (⋃ t ∈ F, ⋂ i ∈ t, E i) ≤ ∑ t ∈ F, μ (⋂ i ∈ t, E i) :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ t ∈ F, p ^ q := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' : t ⊆ s ∧ q ≤ (t.card : ℝ) := by
        simpa only [F, Finset.mem_filter, Finset.mem_powerset] using ht
      rw [hE.meas_biInter t]
      calc
        ∏ i ∈ t, μ (E i) ≤ ∏ _i ∈ t, p :=
          Finset.prod_le_prod' (fun i hi => hprob i (ht'.1 hi))
        _ = p ^ t.card := by simp
        _ = p ^ (t.card : ℝ) := (ENNReal.rpow_natCast p t.card).symm
        _ ≤ p ^ q := ENNReal.rpow_le_rpow_of_exponent_ge hp ht'.2
    _ = (F.card : ℝ≥0∞) * p ^ q := by simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ≥0∞) ^ s.card * p ^ q := by
      apply mul_le_mul_left
      exact_mod_cast hFcard

theorem measure_exists_many_independent_events_le
    {Ω ι κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : κ → ι → Set Ω) (s : Finset ι) (powers : Finset κ)
    (hE : ∀ k ∈ powers, iIndepSet (E k) μ)
    {p : ℝ≥0∞} (hp : p ≤ 1)
    (hprob : ∀ k ∈ powers, ∀ i ∈ s, μ (E k i) ≤ p) (q : ℝ) :
    μ {ω | ∃ k ∈ powers, ∃ t : Finset ι,
      t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} ≤
      (powers.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ s.card * p ^ q) := by
  classical
  have hset : {ω | ∃ k ∈ powers, ∃ t : Finset ι,
      t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} =
      ⋃ k ∈ powers, {ω | ∃ t : Finset ι,
        t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} := by
    ext ω
    simp
  rw [hset]
  calc
    _ ≤ ∑ k ∈ powers, μ {ω | ∃ t : Finset ι,
        t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} :=
      measure_biUnion_finset_le powers _
    _ ≤ ∑ _k ∈ powers, (2 : ℝ≥0∞) ^ s.card * p ^ q := by
      apply Finset.sum_le_sum
      intro k hk
      exact measure_many_independent_events_le μ (E k) (hE k hk) s hp
        (hprob k hk) q
    _ = _ := by simp [nsmul_eq_mul]

theorem exists_many_misses_of_few_successes {ι : Type*} (s : Finset ι)
    (good : ι → Prop) [DecidablePred good]
    (hgood : ((s.filter good).card : ℝ) < (s.card : ℝ) / 20) :
    ∃ t : Finset ι, t ⊆ s ∧ (19 / 20 : ℝ) * s.card < (t.card : ℝ) ∧
      ∀ i ∈ t, ¬ good i := by
  classical
  refine ⟨s.filter (fun i => ¬ good i), Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard := Finset.card_filter_add_card_filter_not (s := s) good
    have hcardR : ((s.filter good).card : ℝ) +
        ((s.filter (fun i => ¬ good i)).card : ℝ) = s.card := by
      exact_mod_cast hcard
    linarith
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRepresentative
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem measurePreserving_productRepresentative {ι : Type*} (i : ι) :
    MeasurePreserving
      (fun x : ι → UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  exact measurePreserving_circleRepresentative.comp
    (measurePreserving_eval_infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)) i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CocycleSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.CocycleSupport

theorem uniform_floor_ne_zero_le (t : ℝ) :
    (volume.restrict (Ico (0 : ℝ) 1)) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ≤
      ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  rw [Measure.restrict_apply hm]
  rcases le_or_gt 0 t with ht | ht
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico (1 - t) 1) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨?_, hx1⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, abs_of_nonneg ht]
        congr 1
        ring
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico 0 (-t)) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨hx0, ?_⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, sub_zero, abs_of_neg ht]

theorem ae_finite_support_of_tsum_ne_top {Ω ι A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Zero A]
    (μ : Measure Ω) (a : ι → Ω → A)
    (h : (∑' i, μ {x | a i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i => a i x)).Finite := by
  exact ae_finite_setOfPred_mem h

theorem ae_all_finite_support_of_tsum_ne_top {Ω ι K A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Countable K] [Zero A]
    (μ : Measure Ω) (a : K → ι → Ω → A)
    (h : ∀ k, (∑' i, μ {x | a k i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ k, (Function.support (fun i => a k i x)).Finite := by
  rw [ae_all_iff]
  intro k
  exact ae_finite_support_of_tsum_ne_top μ (a k) (h k)

theorem measure_floor_ne_zero_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u : Ω → ℝ) (hu : Measurable u)
    (hlaw : μ.map u = volume.restrict (Ico (0 : ℝ) 1)) (t : ℝ) :
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} ≤ ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  calc
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} =
        (μ.map u) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
      (Measure.map_apply hu hm).symm
    _ = (volume.restrict (Ico (0 : ℝ) 1))
        {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} := by rw [hlaw]
    _ ≤ ENNReal.ofReal |t| := uniform_floor_ne_zero_le t

theorem ae_all_int_finite_floor_support {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (u : ι → Ω → ℝ) (hu : ∀ i, Measurable (u i))
    (hlaw : ∀ i, μ.map (u i) = volume.restrict (Ico (0 : ℝ) 1))
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => (⌊u i x + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  apply ae_all_finite_support_of_tsum_ne_top
  intro k
  apply ne_top_of_le_ne_top ((hθ.mul_left |(k : ℝ)|).tsum_ofReal_ne_top)
  apply ENNReal.tsum_le_tsum
  intro i
  simpa only [abs_mul, abs_of_nonneg (hθ0 i)] using
    measure_floor_ne_zero_le μ (u i) (hu i) (hlaw i) ((k : ℝ) * θ i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem ae_product_all_int_finite_floor_support {ι : Type*} [Countable ι]
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))),
      ∀ k : ℤ,
        (Function.support (fun i =>
          (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  exact ae_all_int_finite_floor_support
    (Ω := ι → UnitAddCircle) (ι := ι)
    (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
    (fun i => (measurePreserving_productRepresentative i).measurable)
    (fun i => (measurePreserving_productRepresentative i).map_eq)
    θ hθ0 hθ

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FloorCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace FloorCocycle

theorem floor_fract_add (x y : ℝ) :
    ⌊Int.fract x + y⌋ + ⌊x⌋ = ⌊x + y⌋ := by
  rw [Int.fract, sub_add_eq_add_sub, Int.floor_sub_intCast]
  omega

theorem floor_cocycle (u α : ℝ) (v n : ℤ) :
    ⌊u + (v : ℝ) * α⌋ + ⌊Int.fract (u + (v : ℝ) * α) + (n : ℝ) * α⌋ =
      ⌊u + ((v + n : ℤ) : ℝ) * α⌋ := by
  rw [add_comm, floor_fract_add]
  congr 1
  push_cast
  ring

theorem floor_add_eq_indicator {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u < 1) (t : ℝ) :
    ⌊u + t⌋ = ⌊t⌋ + if 1 - Int.fract t ≤ u then 1 else 0 := by
  have hsplit : ⌊u + t⌋ = ⌊u + Int.fract t⌋ + ⌊t⌋ := by
    rw [← Int.floor_add_intCast]
    congr 1
    rw [add_assoc, Int.fract_add_floor]
  rw [hsplit]
  split_ifs with h
  · have hf : ⌊u + Int.fract t⌋ = 1 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num
        linarith
      · norm_num
        linarith [Int.fract_lt_one t]
    rw [hf]
    omega
  · have hf : ⌊u + Int.fract t⌋ = 0 := by
      apply Int.floor_eq_zero_iff.mpr
      constructor
      · exact add_nonneg hu₀ (Int.fract_nonneg t)
      · linarith
    rw [hf]
    omega

end FloorCocycle
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Function

namespace Invariant233.FiniteSupportCocycle

theorem summable_weighted_int {I : Type*} (c : I → ℝ) {a : I → ℤ}
    (ha : HasFiniteSupport a) : Summable (fun i ↦ c i * (a i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  exact HasFiniteSupport.mul_right c (ha.fun_comp (by simp))

theorem exp_tsum_floor_cocycle {I : Type*} (x θ c : I → ℝ) (k n : ℤ)
    (hk : HasFiniteSupport (fun i ↦ ⌊x i + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋)) :
    Real.exp (-(∑' i, c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ))) =
      Real.exp (-(∑' i, c i *
        (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ))) *
      Real.exp (-(∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ))) := by
  have hcoord (i : I) :
      c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ) =
        c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ) +
        c i * (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ) := by
    rw [← FloorCocycle.floor_cocycle]
    push_cast
    ring
  rw [tsum_congr hcoord,
    (summable_weighted_int c hk).tsum_add (summable_weighted_int c hn),
    neg_add, Real.exp_add, mul_comm]

theorem exp_tsum_floor_zero {I : Type*} (x c : I → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    Real.exp (-(∑' i, c i * (⌊x i⌋ : ℝ))) = 1 := by
  have hf (i : I) : ⌊x i⌋ = 0 := Int.floor_eq_zero_iff.mpr (hx i)
  simp [hf]

end Invariant233.FiniteSupportCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

theorem representative_mem_Ico (x : UnitAddCircle) :
    representative x ∈ Ico (0 : ℝ) 1 := by
  simpa only [representative, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 x).property

theorem representative_add (x : UnitAddCircle) (t : ℝ) :
    representative (x + (t : UnitAddCircle)) = Int.fract (representative x + t) := by
  have hx : x + (t : UnitAddCircle) =
      ((representative x + t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, coe_representative]
  rw [hx]
  change ((AddCircle.equivIco (1 : ℝ) 0
    ((representative x + t : ℝ) : UnitAddCircle)) : ℝ) = _
  simpa only [div_one, mul_one] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (representative x + t))

theorem representative_rotate {I : Type*} (θ : I → ℝ) (k : ℤ)
    (x : Space I) (i : I) :
    representative (rotate θ k x i) =
      Int.fract (representative (x i) + (k : ℝ) * θ i) :=
  representative_add (x i) ((k : ℝ) * θ i)

theorem cocycleVersion_pos {I : Type*} (θ c : I → ℝ) (k : ℤ) (x : Space I) :
    0 < cocycleVersion θ c k x :=
  Real.exp_pos _

@[simp] theorem cocycleVersion_zero {I : Type*} (θ c : I → ℝ) (x : Space I) :
    cocycleVersion θ c 0 x = 1 := by
  simp only [cocycleVersion, Int.cast_zero, zero_mul, add_zero]
  exact FiniteSupportCocycle.exp_tsum_floor_zero _ c
    (fun i ↦ representative_mem_Ico (x i))

theorem cocycleVersion_add_of_finite_support {I : Type*}
    (θ c : I → ℝ) (k n : ℤ) (x : Space I)
    (hk : HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊representative (rotate θ k x i) + (n : ℝ) * θ i⌋)) :
    cocycleVersion θ c (k + n) x =
      cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x := by
  simp only [cocycleVersion, representative_rotate] at hn ⊢
  exact FiniteSupportCocycle.exp_tsum_floor_cocycle _ θ c k n hk hn

theorem exists_invariant_cocycle_core {I : Type*} [Countable I]
    (θ : I → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∃ s : Set (Space I), MeasurableSet s ∧ (∀ᵐ x ∂haar I, x ∈ s) ∧
      (∀ k : ℤ, rotate θ k ⁻¹' s = s) ∧
      (∀ x ∈ s, ∀ k : ℤ, HasFiniteSupport
        (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋)) ∧
      (∀ x ∈ s, ∀ (c : I → ℝ) (k n : ℤ),
        cocycleVersion θ c (k + n) x =
          cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x) := by
  have hall : ∀ᵐ x ∂haar I, ∀ k : ℤ, HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋) :=
    CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  obtain ⟨s, hs, hfull, hprop, hinv⟩ :=
    Invariant233.exists_invariant_conull_forall (rotate θ) (rotate_zero θ)
      (rotate_add θ) (measurePreserving_rotate θ)
      (fun (k : ℤ) (x : Space I) ↦ HasFiniteSupport
        (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
      (ae_all_iff.mp hall)
  have hsupport (x : Space I) (hx : x ∈ s) (k : ℤ) :
      HasFiniteSupport (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋) := by
    simpa only [rotate_zero] using hprop x hx 0 k
  refine ⟨s, hs, hfull, hinv, hsupport, ?_⟩
  intro x hx c k n
  exact cocycleVersion_add_of_finite_support θ c k n x
    (hsupport x hx k) (hprop x hx k n)

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductWeightBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped ENNReal

namespace Invariant233.ProductModel

theorem cost_summand_nonneg (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base) (i : ℕ) :
    0 ≤ c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) := by
  apply mul_nonneg (hc i)
  have hf : (0 : ℤ) ≤ ⌊circleRepresentative (x i) + θ i⌋ := by
    apply Int.floor_nonneg.mpr
    exact add_nonneg (ProductCocycle.representative_mem_Ico (x i)).1 (hθ i)
  exact_mod_cast hf

theorem logarithmicCost_eq_ofReal_tsum (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    logarithmicCost θ c x =
      ENNReal.ofReal (∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ)) := by
  exact (ENNReal.ofReal_tsum_of_nonneg
    (cost_summand_nonneg θ c hθ hc x)
    (FiniteSupportCocycle.summable_weighted_int c hx)).symm

theorem weight_eq_cocycleVersion_of_finite_support (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    weight θ c x = ProductCocycle.cocycleVersion θ c 1 x := by
  have hnonneg : 0 ≤ ∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) :=
    tsum_nonneg (cost_summand_nonneg θ c hθ hc x)
  unfold weight
  rw [logarithmicCost_eq_ofReal_tsum θ c hθ hc x hx,
    EReal.coe_ennreal_ofReal, max_eq_left hnonneg, ← EReal.coe_neg,
    EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [ProductCocycle.cocycleVersion, Int.cast_one, one_mul,
    circleRepresentative, ProductCocycle.representative]

theorem negLogCost_weight (θ c : ℕ → ℝ) (x : Base) :
    negLogCost (weight θ c x) = logarithmicCost θ c x :=
  negLogCost_extendedExpNeg _

theorem weight_ae_eq_cocycleVersion (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    weight θ c =ᵐ[baseMeasure] ProductCocycle.cocycleVersion θ c 1 := by
  have hall := CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  filter_upwards [hall] with x hx
  apply weight_eq_cocycleVersion_of_finite_support θ c hθ0 hc x
  simpa only [HasFiniteSupport, circleRepresentative, Int.cast_one, one_mul] using hx 1

theorem ae_weight_pos (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, 0 < weight θ c x := by
  filter_upwards [weight_ae_eq_cocycleVersion θ c hθ0 hc hθ] with x hx
  rw [hx]
  exact ProductCocycle.cocycleVersion_pos θ c 1 x

theorem lintegral_negLogCost_weight (θ c : ℕ → ℝ) :
    (∫⁻ x, negLogCost (weight θ c x) ∂baseMeasure) =
      ∫⁻ x, logarithmicCost θ c x ∂baseMeasure := by
  simp only [negLogCost_weight]

theorem hasNegInfiniteLogIntegral_iff (θ c : ℕ → ℝ) :
    HasNegInfiniteLogIntegral baseMeasure (weight θ c) ↔
      (∫⁻ x, logarithmicCost θ c x ∂baseMeasure) = ∞ := by
  rw [HasNegInfiniteLogIntegral, lintegral_negLogCost_weight]

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductLogIntegral
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel

theorem uniform_floorCost_integral (θ c : ℝ) (hθ : θ ∈ Ico (0 : ℝ) 1)
    (hc : 0 ≤ c) :
    (∫⁻ u : ℝ, ENNReal.ofReal (c * (⌊u + θ⌋ : ℝ))
      ∂(volume.restrict (Ico (0 : ℝ) 1))) = ENNReal.ofReal (c * θ) := by
  classical
  have heq : (fun u : ℝ ↦ ENNReal.ofReal (c * (⌊u + θ⌋ : ℝ))) =ᵐ[
      volume.restrict (Ico (0 : ℝ) 1)]
      (Ici (1 - θ)).indicator (fun _ ↦ ENNReal.ofReal c) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with u hu
    rw [FloorCocycle.floor_add_eq_indicator hu.1 hu.2,
      Int.floor_eq_zero_iff.mpr hθ, Int.fract_eq_self.mpr hθ, zero_add]
    by_cases h : 1 - θ ≤ u
    · simp [h]
    · simp [h]
  have hinter : Ici (1 - θ) ∩ Ico (0 : ℝ) 1 = Ico (1 - θ) 1 := by
    ext u
    constructor
    · rintro ⟨ha, _, hb⟩
      exact ⟨ha, hb⟩
    · intro hu
      exact ⟨hu.1, by linarith [hu.1, hθ.2], hu.2⟩
  rw [lintegral_congr_ae heq, lintegral_indicator_const measurableSet_Ici,
    Measure.restrict_apply measurableSet_Ici, hinter, Real.volume_Ico]
  rw [show (1 : ℝ) - (1 - θ) = θ by ring, ← ENNReal.ofReal_mul hc]

theorem measurable_cost_summand (θ c : ℕ → ℝ) (i : ℕ) :
    Measurable (fun x : Base ↦
      ENNReal.ofReal (c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ))) := by
  have hrep : Measurable (fun x : Base ↦ circleRepresentative (x i)) :=
    ProductCocycle.measurable_representative.comp (measurable_pi_apply i)
  exact (measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
    ((hrep.add_const (θ i)).floor))).ennreal_ofReal

theorem lintegral_cost_summand (θ c : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) (i : ℕ) :
    (∫⁻ x, ENNReal.ofReal (c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ))
      ∂baseMeasure) = ENNReal.ofReal (c i * θ i) := by
  have hm : Measurable (fun u : ℝ ↦ ENNReal.ofReal (c i * (⌊u + θ i⌋ : ℝ))) :=
    (measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
      ((measurable_id.add_const (θ i)).floor))).ennreal_ofReal
  calc
    _ = ∫⁻ u : ℝ, ENNReal.ofReal (c i * (⌊u + θ i⌋ : ℝ))
        ∂(volume.restrict (Ico (0 : ℝ) 1)) :=
      (CocycleSupport.measurePreserving_productRepresentative i).lintegral_comp hm
    _ = ENNReal.ofReal (c i * θ i) := uniform_floorCost_integral _ _ (hθ i) (hc i)

theorem lintegral_logarithmicCost (θ c : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) :
    (∫⁻ x, logarithmicCost θ c x ∂baseMeasure) =
      ∑' i, ENNReal.ofReal (c i * θ i) := by
  unfold logarithmicCost
  rw [lintegral_tsum (fun i ↦ (measurable_cost_summand θ c i).aemeasurable)]
  exact tsum_congr (lintegral_cost_summand θ c hθ hc)

theorem hasNegInfiniteLogIntegral_iff_tsum (θ c : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) :
    HasNegInfiniteLogIntegral baseMeasure (weight θ c) ↔
      (∑' i, ENNReal.ofReal (c i * θ i)) = ∞ := by
  rw [hasNegInfiniteLogIntegral_iff, lintegral_logarithmicCost θ c hθ hc]

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductBlockCost
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

theorem one_le_block_cost {m : ℕ} (hm : 0 < m) (K C : ℝ)
    (hK : 1 ≤ K) (hC : K ^ 2 ≤ C) (θ : Fin m → ℝ)
    (hθ : ∀ r, 1 / ((m : ℝ) * K) ≤ θ r) :
    (1 : ℝ≥0∞) ≤ ∑' r, ENNReal.ofReal (C * θ r) := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hC0 : 0 ≤ C := le_trans (sq_nonneg K) hC
  have hθ0 (r : Fin m) : 0 ≤ θ r :=
    (le_of_lt (one_div_pos.mpr (mul_pos hmpos hKpos))).trans (hθ r)
  have hlower : C / K ≤ ∑ r : Fin m, C * θ r := by
    calc
      C / K = ∑ _r : Fin m, C * (1 / ((m : ℝ) * K)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      _ ≤ ∑ r : Fin m, C * θ r :=
        Finset.sum_le_sum (fun r _ ↦ mul_le_mul_of_nonneg_left (hθ r) hC0)
  have hone : 1 ≤ C / K := by
    apply (le_div_iff₀ hKpos).mpr
    nlinarith
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
    (fun r _ ↦ mul_nonneg hC0 (hθ0 r))]
  exact ENNReal.one_le_ofReal.mpr (hone.trans hlower)

theorem tsum_block_coordinate_cost_eq_top
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    (∑' i, ENNReal.ofReal (C (e i).1 * θ i)) = ∞ := by
  rw [← e.symm.tsum_eq (fun i : ℕ ↦ ENNReal.ofReal (C (e i).1 * θ i))]
  simp only [e.apply_symm_apply]
  rw [ENNReal.tsum_sigma (fun (j : ℕ) (r : Fin (m j)) ↦
    ENNReal.ofReal (C j * θ (e.symm ⟨j, r⟩)))]
  apply top_le_iff.mp
  calc
    (∞ : ℝ≥0∞) = ∑' _j : ℕ, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∑' j, ∑' r : Fin (m j), ENNReal.ofReal (C j * θ (e.symm ⟨j, r⟩)) := by
      apply ENNReal.tsum_le_tsum
      intro j
      apply one_le_block_cost (hm j) (K j) (C j) (hK j) (hC j)
      intro r
      simpa only [e.apply_symm_apply] using hθ (e.symm ⟨j, r⟩)

theorem hasNegInfiniteLogIntegral_of_block_bounds
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hθ : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i ↦ C (e i).1)) := by
  apply (hasNegInfiniteLogIntegral_iff_tsum θ _ hθ01
    (fun i ↦ le_trans (sq_nonneg _) (hC (e i).1))).mpr
  exact tsum_block_coordinate_cost_eq_top m hm K C hK hC e θ hθ

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedShiftPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.shift_zero _root_.OAI.Invariant233.WeightedShift.translate_add _root_.OAI.Invariant233.WeightedShift.translate_apply _root_.OAI.Invariant233.WeightedShift.translate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal BigOperators
namespace Invariant233.WeightedShift

theorem operator_pow_apply_add (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) (k + n) =
      (∏ j ∈ Finset.range n, w (k + j)) * ξ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, operator_apply]
    have hk : k + (↑(n + 1) : ℤ) - 1 = k + n := by omega
    rw [hk, ih, Finset.prod_range_succ]
    ring

theorem operator_pow_apply (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) k =
      (∏ j ∈ Finset.range n, w (k - n + j)) * ξ (k - n) := by
  simpa using operator_pow_apply_add w n ξ (k - n)

theorem norm_operator_pow_le (w : Weight) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ k : ℤ, ‖∏ j ∈ Finset.range n, w (k + j)‖ ≤ B) :
    ‖(operator w)^n‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro ξ
  calc
    ‖((operator w)^n) ξ‖ ≤ ‖B • shift (n : ℤ) ξ‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro k
      simp only [operator_pow_apply, norm_mul, lp.coeFn_smul, Pi.smul_apply,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hB, shift_apply]
      exact mul_le_mul_of_nonneg_right (hprod (k - n)) (norm_nonneg _)
    _ = B * ‖ξ‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hB,
      (shift (n : ℤ)).norm_map]

theorem norm_product_le_norm_operator_pow (w : Weight) (n : ℕ) (k : ℤ) :
    ‖∏ j ∈ Finset.range n, w (k + j)‖ ≤ ‖(operator w)^n‖ := by
  let ξ : Hilbert := lp.single 2 k 1
  have hξ : ‖ξ‖ = 1 := by simp [ξ, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  have heval : (((operator w)^n) ξ) (k + n) =
      ∏ j ∈ Finset.range n, w (k + j) := by
    rw [operator_pow_apply_add]
    simp [ξ]
  calc
    ‖∏ j ∈ Finset.range n, w (k + j)‖ =
        ‖(((operator w)^n) ξ) (k + n)‖ := congrArg norm heval.symm
    _ ≤ ‖((operator w)^n) ξ‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖(operator w)^n‖ * ‖ξ‖ := ((operator w)^n).le_opNorm ξ
    _ = ‖(operator w)^n‖ := by rw [hξ, mul_one]

theorem norm_operator_pow (w : Weight) (n : ℕ) :
    ‖(operator w)^n‖ = ‖orbitProduct w n‖ := by
  apply le_antisymm
  · apply norm_operator_pow_le w n (norm_nonneg _)
    intro k
    exact lp.norm_apply_le_norm (by simp) (orbitProduct w n) k
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro k
    exact norm_product_le_norm_operator_pow w n k

@[simp] theorem norm_operator (w : Weight) : ‖operator w‖ = ‖w‖ := by
  have h : orbitProduct w 1 = w := by ext k; simp [orbitProduct_apply]
  simpa [h] using norm_operator_pow w 1

@[simp] theorem operator_eq_zero_iff (w : Weight) : operator w = 0 ↔ w = 0 := by
  rw [← norm_eq_zero, norm_operator, norm_eq_zero]

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal lp Topology

namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)

variable {a C hC ha hm}

theorem fieldShift_ae (m : ℤ) (f : Lp Hilbert 2 μ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f =ᵐ[μ]
      fun x => shift m (f x) :=
  ContinuousLinearMap.coeFn_compLp _ f

theorem fieldShift_add (m n : ℤ) :
    (shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ =
      (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
        (shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  ext f
  filter_upwards [fieldShift_ae (m + n) f,
    fieldShift_ae m ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f),
    fieldShift_ae n f] with x hmn hm hn
  change ((shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x =
    ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
      ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f)) x
  rw [hmn, hm, hn]
  exact congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (f x)) (shift_add m n)

theorem fieldShift_zero :
    (shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ = 1 := by
  ext f
  filter_upwards [fieldShift_ae 0 f] with x hx
  change ((shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x = f x
  rw [hx]
  change (shift 0).toLinearIsometry.toContinuousLinearMap (f x) = f x
  rw [shift_zero]
  rfl

theorem fieldShift_norm_map (m : ℤ) (f : Lp Hilbert 2 μ) :
    ‖(shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f‖ = ‖f‖ := by
  have hnorm : ∀ᵐ x ∂μ,
      ‖((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x‖ = ‖f x‖ := by
    filter_upwards [fieldShift_ae m f] with x hx
    rw [hx, (shift m).norm_map]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.symm.le))

theorem fieldShift_mem_unitary (m : ℤ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ ∈
      unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  let A := (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  let B := (shift (-m)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  have hAB : A * B = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hA : IsUnit A := ⟨⟨A, B, hAB, hBA⟩, rfl⟩
  apply hA.mem_unitary_iff_star_mul_self.mpr
  change ContinuousLinearMap.adjoint A ∘L A = 1
  exact A.norm_map_iff_adjoint_comp_self.mp (fieldShift_norm_map m)

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ScalarDeterminantZero
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Invariant233.ScalarDeterminant

theorem log_sq_add_sq_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    Real.log (a ^ 2 + t ^ 2) ≤ Real.log 2 + 2 * Real.log (max a t) := by
  have hm : 0 < max a t := ht.trans_le (le_max_right a t)
  have ha2 := pow_le_pow_left₀ ha (le_max_left a t) 2
  have ht2 := pow_le_pow_left₀ ht.le (le_max_right a t) 2
  have hlog : Real.log (a ^ 2 + t ^ 2) ≤ Real.log (2 * (max a t) ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  calc
    _ ≤ Real.log (2 * (max a t) ^ 2) := hlog
    _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ hm.ne'), Real.log_pow]; norm_num

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem integrable_regularized_log {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x => Real.log (f x ^ 2 + ε)) μ := by
  refine (integrable_const (|Real.log ε| + |Real.log (1 + ε)|)).mono'
    ((hf.pow_const 2 |>.add_const ε).log.aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hx := hbound x
  have hlo : Real.log ε ≤ Real.log (f x ^ 2 + ε) :=
    Real.log_le_log hε (le_add_of_nonneg_left (sq_nonneg _))
  have hhi : Real.log (f x ^ 2 + ε) ≤ Real.log (1 + ε) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (Real.log ε)
    have := abs_nonneg (Real.log (1 + ε))
    linarith
  · have := le_abs_self (Real.log (1 + ε))
    have := abs_nonneg (Real.log ε)
    linarith

theorem integrable_truncated_log {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {M : ℝ} (hM : 0 < M) :
    Integrable (fun x => Real.log (max (f x) (Real.exp (-M)))) μ := by
  refine (integrable_const M).mono'
    ((hf.max measurable_const).log.aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hp : 0 < max (f x) (Real.exp (-M)) :=
    (Real.exp_pos _).trans_le (le_max_right _ _)
  have hlo : -M ≤ Real.log (max (f x) (Real.exp (-M))) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos (-M)) (le_max_right (f x) (Real.exp (-M)))
  have hhi : Real.log (max (f x) (Real.exp (-M))) ≤ 0 := by
    apply Real.log_nonpos hp.le
    exact max_le (hbound x).2 (Real.exp_le_one_iff.mpr (by linarith))
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hlo, hhi.trans hM.le⟩

variable [IsProbabilityMeasure μ]

theorem integral_regularized_log_le {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {M : ℝ} (hM : 0 < M) :
    (∫ x, Real.log (f x ^ 2 + (Real.exp (-M)) ^ 2) ∂μ) ≤
      Real.log 2 + 2 * ∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ := by
  have hint := integrable_truncated_log (μ := μ) hf hbound hM
  calc
    _ ≤ ∫ x, Real.log 2 + 2 * Real.log (max (f x) (Real.exp (-M))) ∂μ :=
      integral_mono (integrable_regularized_log hf hbound (sq_pos_of_pos (Real.exp_pos _)))
        ((integrable_const _).add (hint.const_mul 2))
        (fun x => log_sq_add_sq_le (hbound x).1 (Real.exp_pos _))
    _ = _ := by
      rw [integral_add (integrable_const _) (hint.const_mul 2), integral_const_mul]
      simp

theorem regularized_determinant_eq_zero {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (htrunc : ∀ B : ℝ, ∃ M : ℝ, 0 < M ∧
      (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) < B) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
      (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) = 0 := by
  apply le_antisymm _ bot_le
  have hlow (n : ℕ) :
      (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
    obtain ⟨M, hM, hsmall⟩ := htrunc (-(n : ℝ) - Real.log 2 / 2)
    have hint := integral_regularized_log_le (μ := μ) hf hbound hM
    calc
      _ ≤ ENNReal.ofReal (Real.exp
          ((∫ x, Real.log (f x ^ 2 + (Real.exp (-M)) ^ 2) ∂μ) / 2)) :=
        iInf_le _ (⟨(Real.exp (-M)) ^ 2, sq_pos_of_pos (Real.exp_pos _)⟩ : {r : ℝ // 0 < r})
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        linarith
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(n : ℝ))))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)
  exact ge_of_tendsto' hlim hlow


end Invariant233.ScalarDeterminant

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_SpectralNaturality
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal CStarAlgebra

namespace Invariant233

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma regularizedNormSquare_spectrum_pos (a : A) (ε : ℝ) (hε : 0 < ε) :
    ∀ x ∈ spectrum ℝ (star a * a + ε • (1 : A)), 0 < x := by
  intro x hx
  rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.add_singleton_eq] at hx
  obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_add.mp hx
  have ht' : t = ε := Set.mem_singleton_iff.mp ht
  subst t
  linarith [spectrum_star_mul_self_nonneg y hy]

lemma regularizedLog_map (φ : A →⋆ₐ[ℂ] B) (a : A) (ε : ℝ) (hε : 0 < ε) :
    φ (CFC.log (star a * a + ε • (1 : A))) =
      CFC.log (star (φ a) * φ a + ε • (1 : B)) := by
  have hp := regularizedNormSquare_spectrum_pos a ε hε
  have hc : ContinuousOn Real.log (spectrum ℝ (star a * a + ε • (1 : A))) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (hp x hx)
  have hs : IsSelfAdjoint (star a * a + ε • (1 : A)) := by
    simp [IsSelfAdjoint]
  have hφs : IsSelfAdjoint (φ (star a * a + ε • (1 : A))) := by
    change star (φ _) = φ _
    rw [← map_star, hs.star_eq]
  have hsmul : φ (ε • (1 : A)) = ε • (1 : B) := by
    calc
      φ (ε • (1 : A)) = ε • φ 1 := φ.toAlgHom.map_smul_of_tower ε 1
      _ = ε • (1 : B) := by rw [map_one]
  rw [CFC.log, φ.map_cfc Real.log _ hc (by fun_prop) hs hφs]
  simp only [map_add, map_mul, map_star, hsmul, CFC.log]

lemma regularizedLog_complex (z : ℂ) (ε : ℝ) :
    CFC.log (star z * z + ε • (1 : ℂ)) =
      (Real.log (‖z‖ ^ 2 + ε) : ℂ) := by
  have h : star z * z + ε • (1 : ℂ) =
      algebraMap ℝ ℂ (‖z‖ ^ 2 + ε) := by
    simp only [Complex.star_def, Complex.conj_mul', Complex.real_smul, mul_one,
      Complex.coe_algebraMap, Complex.ofReal_add, Complex.ofReal_pow]
  rw [h, CFC.log_algebraMap]
  rfl

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_DeterminantWeightBridge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233

theorem ScalarDeterminant.regularized_determinant_eq_zero_of_log_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hm : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) (hinf : HasNegInfiniteLogIntegral μ f) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
      (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) = 0 := by
  apply ScalarDeterminant.regularized_determinant_eq_zero hm hbound
  intro B
  obtain ⟨M, hM, hlt⟩ := exists_pos_truncated_log_integral_lt f hm
    (fun x => (hbound x).1) (fun x => (hbound x).2) hpos
    ((hasNegInfiniteLogIntegral_iff_of_ae_pos f hpos).mp hinf) (-B / 2)
  refine ⟨M, hM, ?_⟩
  linarith

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_RotationDeterminant
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal CStarAlgebra
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorFugledeKadisonDeterminant_unitary_mul (ξ : H)
    (u : unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    vectorFugledeKadisonDeterminant ξ ((u : H →L[ℂ] H) * T) =
      vectorFugledeKadisonDeterminant ξ T := by
  have h : star ((u : H →L[ℂ] H) * T) * ((u : H →L[ℂ] H) * T) = star T * T := by
    rw [star_mul, mul_assoc, ← mul_assoc (star (u : H →L[ℂ] H)),
      Unitary.star_mul_self_of_mem u.property]
    simp
  simp only [vectorFugledeKadisonDeterminant, h]

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductMultiplierFunctionalCalculus
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem vectorTrace_multiplier (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    vectorTrace traceVector (multiplier θ g C hC hg hb) = ∫ x, g x ∂baseMeasure := by
  change inner ℂ traceVector (multiplier θ g C hC hg hb traceVector) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  have hv : traceVector =ᵐ[baseMeasure]
      fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) := Lp.coeFn_const 2 baseMeasure _
  filter_upwards [hv, multiplier_coordinates_ae θ g C hC hg hb traceVector] with x hv hm
  rw [hv, lp.inner_single_left]
  rw [hm 0, hv]
  simp
  congr 1
  funext i
  simp [Invariant233.ProductModel.rotationIterate]

section ContinuousValues
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem vectorTrace_continuousValueRepresentation (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f : C(Y, ℂ)) :
    vectorTrace traceVector (continuousValueRepresentation θ a ha f) =
      ∫ x, f (a x) ∂baseMeasure :=
  vectorTrace_multiplier θ (fun x => f (a x)) ‖f‖ (norm_nonneg f)
    (f.continuous.measurable.comp ha) (fun x => f.norm_coe_le_norm (a x))

end ContinuousValues
end Invariant233.ProductModel

namespace Invariant233

theorem vectorFugledeKadisonDeterminant_composed_representation
    {H X Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (μ : Measure X) (a : X → Y)
    (π : C(Y, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hξ : ∀ g : C(Y, ℂ), vectorTrace ξ (π g) = ∫ x, g (a x) ∂μ)
    (f : C(Y, ℂ)) :
    vectorFugledeKadisonDeterminant ξ (π f) =
      ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (‖f (a x)‖ ^ 2 + ε.val) ∂μ) / 2)) := by
  let : NormedAlgebra ℝ C(Y, ℂ) := NormedAlgebra.restrictScalars ℝ ℂ C(Y, ℂ)
  unfold vectorFugledeKadisonDeterminant
  apply iInf_congr
  intro ε
  rw [← regularizedLog_map π f ε.val ε.property, hξ]
  have hpoint : ∀ y, (CFC.log (star f * f + ε.val • (1 : C(Y, ℂ)))) y =
      (Real.log (‖f y‖ ^ 2 + ε.val) : ℂ) := by
    intro y
    have h := regularizedLog_map (ContinuousMap.evalStarAlgHom ℂ ℂ y) f ε.val ε.property
    simpa only [ContinuousMap.evalStarAlgHom_apply] using
      h.trans (regularizedLog_complex (f y) ε.val)
  simp_rw [hpoint]
  rw [integral_complex_ofReal]
  rfl

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductNorm
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology ENNReal

namespace Invariant233.ProductNorm

theorem floor_lower_bound (x t : ℝ) (hx : 0 ≤ x) :
    t - 1 ≤ (⌊x + t⌋ : ℝ) := by
  have h := Int.sub_one_lt_floor (x + t)
  linarith

theorem finite_cost_lower_bound {ι : Type*} (I : Finset ι)
    (c x θ : ι → ℝ) (n : ℕ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hx : ∀ i ∈ I, 0 ≤ x i) :
    (n : ℝ) * (∑ i ∈ I, c i * θ i) - (∑ i ∈ I, c i) ≤
      ∑ i ∈ I, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ) := by
  calc
    (n : ℝ) * (∑ i ∈ I, c i * θ i) - (∑ i ∈ I, c i) =
        ∑ i ∈ I, c i * ((n : ℝ) * θ i - 1) := by
      simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, mul_one]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (floor_lower_bound (x i) ((n : ℝ) * θ i) (hx i hi))
        (hc i hi)

theorem finite_weight_upper_bound {ι : Type*} (I : Finset ι)
    (c x θ : ι → ℝ) (n : ℕ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hx : ∀ i ∈ I, 0 ≤ x i) :
    Real.exp (-(∑ i ∈ I, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) := by
  apply Real.exp_le_exp.mpr
  have h := finite_cost_lower_bound I c x θ n hc hx
  linarith

theorem infinite_weight_upper_bound {ι : Type*} (I : Finset ι)
    (c x θ : ι → ℝ) (n : ℕ)
    (hc : ∀ i, 0 ≤ c i) (hx : ∀ i, 0 ≤ x i) (hθ : ∀ i, 0 ≤ θ i)
    (hsum : Summable (fun i => c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) :
    Real.exp (-(∑' i, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) := by
  have hcost : ∀ i, 0 ≤ c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ) := by
    intro i
    apply mul_nonneg (hc i)
    exact_mod_cast Int.floor_nonneg.mpr (add_nonneg (hx i) (mul_nonneg (Nat.cast_nonneg n) (hθ i)))
  calc
    Real.exp (-(∑' i, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) ≤
        Real.exp (-(∑ i ∈ I, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (Summable.sum_le_tsum I (fun i _hi => hcost i) hsum)
    _ ≤ _ := finite_weight_upper_bound I c x θ n (fun i _ => hc i) (fun i _ => hx i)

theorem root_upper_bound (u C S : ℝ) (n : ℕ) (hn : 0 < n)
    (hu : 0 ≤ u) (h : u ≤ Real.exp (C - (n : ℝ) * S)) :
    u ^ (1 / (n : ℝ)) ≤ Real.exp (C / (n : ℝ) - S) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    u ^ (1 / (n : ℝ)) ≤ Real.exp (C - (n : ℝ) * S) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow hu h (by positivity)
    _ = Real.exp ((C - (n : ℝ) * S) * (1 / (n : ℝ))) :=
      (Real.exp_mul _ _).symm
    _ = Real.exp (C / (n : ℝ) - S) := by
      congr 1
      field_simp

theorem tendsto_root_zero_of_exponential_bounds
    (u C S : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hbound : ∀ q n, 0 < n → u n ≤ Real.exp (C q - (n : ℝ) * S q))
    (hS : ∀ b : ℝ, ∃ q, b < S q) :
    Tendsto (fun n : ℕ => (u n) ^ (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n =>
      lt_of_lt_of_le ha (Real.rpow_nonneg (hu n) _)
  · intro ε hε
    obtain ⟨q, hq⟩ := hS (1 - Real.log ε)
    have hlim : Tendsto (fun n : ℕ => C q / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (C q)
    have hevent : ∀ᶠ n : ℕ in atTop, C q / (n : ℝ) < 1 :=
      hlim.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hevent, Filter.eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    calc
      (u n) ^ (1 / (n : ℝ)) ≤ Real.exp (C q / (n : ℝ) - S q) :=
        root_upper_bound (u n) (C q) (S q) n hnpos (hu n) (hbound q n hnpos)
      _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
      _ = ε := Real.exp_log hε

theorem exists_finite_sum_gt_of_tsum_eq_top {ι : Type*}
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hdiv : (∑' i, ENNReal.ofReal (a i)) = ⊤) (b : ℝ) :
    ∃ I : Finset ι, b < ∑ i ∈ I, a i := by
  classical
  by_cases hb : 0 ≤ b
  · have hlt : ENNReal.ofReal b < ∑' i, ENNReal.ofReal (a i) := by
      rw [hdiv]
      exact ENNReal.ofReal_lt_top
    rw [ENNReal.tsum_eq_iSup_sum] at hlt
    obtain ⟨I, hI⟩ := lt_iSup_iff.mp hlt
    refine ⟨I, ?_⟩
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _hi => ha i)] at hI
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb).mp hI
  · exact ⟨∅, by simpa using lt_of_not_ge hb⟩

end Invariant233.ProductNorm

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldWeightedShiftPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)

theorem fieldOperator_ae (f : Lp Hilbert 2 μ) :
    fieldOperator a C hC ha hm f =ᵐ[μ] fun x => operator (a x) (f x) := by
  filter_upwards [fieldShift_ae 1 (fieldDiagonal a C hC ha hm f),
    fieldDiagonal_ae a C hC ha hm f] with x hs hd
  change ((shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
    (fieldDiagonal a C hC ha hm f)) x = operator (a x) (f x)
  rw [hs, hd]
  rfl

theorem fieldOperator_pow_ae (n : ℕ) (f : Lp Hilbert 2 μ) :
    ((fieldOperator a C hC ha hm)^n) f =ᵐ[μ]
      fun x => ((operator (a x))^n) (f x) := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    filter_upwards [fieldOperator_ae a C hC ha hm
      (((fieldOperator a C hC ha hm)^n) f), ih] with x hx hn
    simpa only [pow_succ', mul_apply_eq_comp, hn] using hx

theorem norm_fieldOperator_pow_le (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ᵐ x ∂μ, ∀ k : ℤ,
      ‖∏ j ∈ Finset.range n, a x (k + j)‖ ≤ B) :
    ‖(fieldOperator a C hC ha hm)^n‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fieldOperator_pow_ae a C hC ha hm n f, hprod] with x hx hb
  rw [hx]
  exact ((operator (a x))^n).le_of_opNorm_le
    (norm_operator_pow_le (a x) n hB hb) (f x)

theorem fieldOperator_eq_zero_iff [IsFiniteMeasure μ] :
    fieldOperator a C hC ha hm = 0 ↔ a =ᵐ[μ] 0 := by
  constructor
  · intro h
    have hk : ∀ k : ℤ, ∀ᵐ x ∂μ, a x k = 0 := by
      intro k
      let f : Lp Hilbert 2 μ := Lp.const 2 μ (lp.single 2 k 1)
      filter_upwards [fieldOperator_ae a C hC ha hm f,
        Lp.coeFn_const 2 μ (lp.single 2 k (1 : ℂ) : Hilbert), Lp.coeFn_zero Hilbert 2 μ]
        with x hx hc hz
      change f x = lp.single 2 k 1 at hc
      change (0 : Lp Hilbert 2 μ) x = 0 at hz
      simp only [h, zero_apply] at hx
      rw [hz, hc] at hx
      have hv := congrArg (fun v : Hilbert => v (k+1)) hx.symm
      simpa [operator_apply] using hv
    filter_upwards [ae_all_iff.mpr hk] with x hx
    apply lp.ext
    funext k
    exact hx k
  · intro h
    ext f
    filter_upwards [fieldOperator_ae a C hC ha hm f, h, Lp.coeFn_zero Hilbert 2 μ]
      with x hx ha0 hz
    change fieldOperator a C hC ha hm f x = (0 : Lp Hilbert 2 μ) x
    simp only [Pi.zero_apply] at ha0 hz
    rw [hx, ha0, (operator_eq_zero_iff 0).2 rfl, zero_apply]
    exact hz.symm

theorem fieldOperator_ne_zero_of_coordinate [IsFiniteMeasure μ] [NeZero μ]
    (k : ℤ) (hpos : ∀ᵐ x ∂μ, a x k ≠ 0) : fieldOperator a C hC ha hm ≠ 0 := by
  intro h
  have hz := (fieldOperator_eq_zero_iff a C hC ha hm).1 h
  obtain ⟨x, hx, hp⟩ := (hz.and hpos).exists
  exact hp (by rw [hx]; rfl)

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductQuasinilpotent
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel

theorem weight_orbit_product_eq_cocycleVersion
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (s : Set Base) (hinv : ∀ k : ℤ, ProductCocycle.rotate θ k ⁻¹' s = s)
    (hs : ∀ x ∈ s, ∀ k : ℤ, HasFiniteSupport
      (fun i ↦ ⌊ProductCocycle.representative (x i) + (k : ℝ) * θ i⌋))
    (hlaw : ∀ x ∈ s, ∀ k n : ℤ,
      ProductCocycle.cocycleVersion θ c (k + n) x =
        ProductCocycle.cocycleVersion θ c n (ProductCocycle.rotate θ k x) *
          ProductCocycle.cocycleVersion θ c k x)
    (x : Base) (hx : x ∈ s) (n : ℕ) :
    (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ j x)) =
      ProductCocycle.cocycleVersion θ c n x := by
  have hweight (k : ℤ) : weight θ c (rotationIterate θ k x) =
      ProductCocycle.cocycleVersion θ c 1 (ProductCocycle.rotate θ k x) := by
    apply weight_eq_cocycleVersion_of_finite_support θ c hθ0 hc
    have hxk : ProductCocycle.rotate θ k x ∈ s := by
      change x ∈ ProductCocycle.rotate θ k ⁻¹' s
      rw [hinv k]
      exact hx
    simpa only [ProductCocycle.representative, circleRepresentative,
      Int.cast_one, one_mul, rotationIterate, ProductCocycle.rotate] using hs _ hxk 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, hweight]
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using (hlaw x hx n 1).symm

theorem ae_weight_orbit_product_le
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (I : Finset ℕ) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) ≤
        Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) := by
  obtain ⟨s, _hsm, hfull, hinv, hs, hlaw⟩ :=
    ProductCocycle.exists_invariant_cocycle_core θ hθ0 hθ
  filter_upwards [hfull] with x hx k
  have hxk : ProductCocycle.rotate θ k x ∈ s := by
    change x ∈ ProductCocycle.rotate θ k ⁻¹' s
    rw [hinv k]
    exact hx
  have hprod := weight_orbit_product_eq_cocycleVersion θ c hθ0 hc s hinv hs
    (fun y hy => hlaw y hy c) (ProductCocycle.rotate θ k x) hxk n
  have hrot (j : ℕ) : rotationIterate θ (k + j) x =
      rotationIterate θ j (ProductCocycle.rotate θ k x) :=
    ProductCocycle.rotate_add θ k j x
  simp_rw [hrot]
  rw [hprod]
  apply ProductNorm.infinite_weight_upper_bound I c
    (fun i => ProductCocycle.representative (ProductCocycle.rotate θ k x i)) θ n
    hc (fun i => (ProductCocycle.representative_mem_Ico _).1) hθ0
  simpa only [Int.cast_natCast] using
    FiniteSupportCocycle.summable_weighted_int c (hs _ hxk n)

theorem norm_weightedOperator_pow_le
    (θ c : ℕ → ℝ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) ≤ B) :
    ‖weightedOperator θ c ^ n‖ ≤ B := by
  unfold weightedOperator multiplier shiftOperator
  apply WeightedShift.norm_fieldOperator_pow_le
    (multiplierField θ (fun x => (weight θ c x : ℂ)) 1 _) 1 _ _ _ n hB
  filter_upwards [hprod] with x hx k
  change ‖∏ j ∈ Finset.range n,
    (weight θ c (rotationIterate θ (k + j) x) : ℂ)‖ ≤ B
  rw [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg (fun j _hj => (weight_mem_Icc θ c _).1))]
  exact hx k

theorem norm_weightedOperator_pow_le_finite_cost
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (I : Finset ℕ) (n : ℕ) :
    ‖weightedOperator θ c ^ n‖ ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) :=
  norm_weightedOperator_pow_le θ c n (Real.exp_nonneg _)
    (ae_weight_orbit_product_le θ c hθ0 hc hθ I n)

theorem weightedOperator_normQuasinilpotent
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    NormQuasinilpotent (weightedOperator θ c) := by
  classical
  have hex : ∀ q : ℕ, ∃ I : Finset ℕ, (q : ℝ) < ∑ i ∈ I, c i * θ i := by
    intro q
    exact ProductNorm.exists_finite_sum_gt_of_tsum_eq_top (fun i => c i * θ i)
      (fun i => mul_nonneg (hc i) (hθ0 i)) hdiv q
  choose I hI using hex
  apply ProductNorm.tendsto_root_zero_of_exponential_bounds
    (fun n => ‖weightedOperator θ c ^ n‖)
    (fun q => ∑ i ∈ I q, c i) (fun q => ∑ i ∈ I q, c i * θ i)
    (fun n => norm_nonneg _)
  · intro q n _hn
    exact norm_weightedOperator_pow_le_finite_cost θ c hθ0 hc hθ (I q) n
  · intro b
    obtain ⟨q, hq⟩ := exists_nat_gt b
    exact ⟨q, hq.trans (hI q)⟩

theorem weightedOperator_ne_zero
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) : weightedOperator θ c ≠ 0 := by
  unfold weightedOperator multiplier shiftOperator
  apply WeightedShift.fieldOperator_ne_zero_of_coordinate
    (multiplierField θ (fun x => (weight θ c x : ℂ)) 1 _) 1 _ _ _ (0 : ℤ)
  filter_upwards [ae_weight_pos θ c hθ0 hc hθ] with x hx
  change (weight θ c (rotationIterate θ 0 x) : ℂ) ≠ 0
  have hrot : rotationIterate θ 0 x = x := ProductCocycle.rotate_zero θ x
  rw [hrot, Complex.ofReal_ne_zero]
  exact ne_of_gt hx

theorem weightedOperator_spectralRadius_eq_zero
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    spectralRadius ℂ (weightedOperator θ c) = 0 :=
  spectralRadius_zero_of_norm_root_tendsto_zero _
    (weightedOperator_normQuasinilpotent θ c hθ0 hc hθ hdiv)

theorem weightedOperator_spectrum_eq_singleton_zero
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    spectrum ℂ (weightedOperator θ c) = {0} := by
  let : Nontrivial (Hilbert →L[ℂ] Hilbert) :=
    ⟨⟨weightedOperator θ c, 0, weightedOperator_ne_zero θ c hθ0 hc hθ⟩⟩
  exact spectrum_eq_zero_of_spectralRadius_zero _
    (weightedOperator_spectralRadius_eq_zero θ c hθ0 hc hθ hdiv)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem real_K_pos (n : ℕ) : 0 < (p.K n : ℝ) := by exact_mod_cast hp.K_pos n

theorem real_K_double (n : ℕ) : 2 * (p.K n : ℝ) ≤ (p.K (n + 1) : ℝ) := by
  exact_mod_cast (hp.K_double n).le

theorem summable_reciprocal : Summable (fun n => 1 / (p.K n : ℝ)) :=
  ParameterTails.summable_reciprocal hp.real_K_pos hp.real_K_double

theorem m_ge_pow_self (n : ℕ) : 2 ^ n ≤ p.m n := by
  have h := hp.m_ge_pow n
  have hpow : 2 ^ n ≤ 2 ^ (n + 1) := by
    rw [pow_succ]
    omega
  exact hpow.trans h

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleConstruction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233.ProductScaleConstruction

open SamplingHorizon FiniteWindow

private theorem count_eq (n : ℕ) : (states n).count = constructed.prefixCount n := by
  induction n with
  | zero => simp [states, ProductScaleData.prefixCount]
  | succ n ih =>
    change (states n).count + (choices n).m = constructed.prefixCount (n + 1)
    rw [ih]
    simp [ProductScaleData.prefixCount, Finset.sum_range_succ, constructed]

private theorem cost_eq (n : ℕ) : (states n).cost = constructed.prefixCost n := by
  induction n with
  | zero => simp [states, ProductScaleData.prefixCost]
  | succ n ih =>
    change (states n).cost + max (choices n).L (((states n).K : ℝ) ^ 2) *
      (choices n).m = constructed.prefixCost (n + 1)
    rw [ih]
    simp [ProductScaleData.prefixCost, Finset.sum_range_succ, constructed]

theorem constructed_laws : ProductScaleLaws constructed := by
  refine {
    initial_K := rfl
    initial_G := rfl
    K_pos := ?_
    G_pos := ?_
    epsilon_pos := fun n => (choices n).epsilon_pos
    L_ge_one := fun n => (choices n).L_one
    L_monotone := ?_
    C_eq := fun _ => rfl
    polynomial_lower := ?_
    polynomial_attenuation := fun n => (choices n).attenuation
    gain_attenuation := fun n => (choices n).gain
    m_ge_K := fun n => (choices n).m_K
    m_ge_pow := fun n => (choices n).m_pow
    m_ge_G := fun n => (choices n).m_G
    m_ge_100 := fun n => le_trans (by decide) (choices n).m_large
    prefix_count_le := ?_
    m_attenuation := fun n => (choices n).attenuation_m
    next_K := fun _ => rfl
    next_gap := fun n => (choices n).gap
    K_double := fun n => (choices n).double }
  · intro n
    induction n with
    | zero => norm_num [constructed, states]
    | succ n ih =>
      have h := (choices n).double
      change 0 < ⌈((choices n).m : ℝ) ^ ((3 / 4 : ℝ) * (choices n).m)⌉₊
      omega
  · intro n
    cases n with
    | zero => norm_num [constructed, states]
    | succ n => exact Nat.zero_lt_of_lt (choices n).gain_one
  · apply monotone_nat_of_le_succ
    intro n
    exact (choices (n + 1)).L_previous
  · intro n
    unfold ProductScaleData.coefficientBound
    rw [← cost_eq n]
    exact (choices n).polynomial
  · intro n
    rw [← count_eq n]
    exact (choices n).count_bound

theorem exists_product_scales : ∃ p : ProductScaleData, ProductScaleLaws p :=
  ⟨constructed, constructed_laws⟩

end Invariant233.ProductScaleConstruction

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_IntegerPhaseWindow
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ProductPhases

theorem mem_nonzeroIntegerWindow {R : ℝ} {k : ℤ} :
    k ∈ nonzeroIntegerWindow R ↔ k ≠ 0 ∧ |(k : ℝ)| ≤ R := by
  simp only [nonzeroIntegerWindow, Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨hk, hlo, hhi⟩
    refine ⟨hk, abs_le.mpr ⟨?_, Int.le_floor.mp hhi⟩⟩
    have hn : -k ≤ Int.floor R := by omega
    have hh := Int.le_floor.mp hn
    simp only [Int.cast_neg] at hh
    linarith
  · rintro ⟨hk, habs⟩
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hn : -k ≤ Int.floor R := Int.le_floor.mpr (by push_cast <;> linarith)
    exact ⟨hk, by omega, Int.le_floor.mpr hhi⟩

theorem card_nonzeroIntegerWindow {R : ℝ} (hR : 0 ≤ R) :
    ((nonzeroIntegerWindow R).card : ℤ) = 2 * Int.floor R := by
  have hf : 0 ≤ Int.floor R := Int.floor_nonneg.mpr hR
  have hz : (0 : ℤ) ∈ Finset.Icc (-Int.floor R) (Int.floor R) := by
    simp only [Finset.mem_Icc]
    omega
  have he := Finset.card_erase_add_one hz
  have he' : ((nonzeroIntegerWindow R).card : ℤ) + 1 =
      ((Finset.Icc (-Int.floor R) (Int.floor R)).card : ℤ) := by
    exact_mod_cast he
  have hI := Int.card_Icc_of_le (a := -Int.floor R) (b := Int.floor R) (by omega)
  omega

theorem card_nonzeroIntegerWindow_le {R : ℝ} (hR : 0 ≤ R) :
    ((nonzeroIntegerWindow R).card : ℝ) ≤ 2 * R := by
  have he : ((nonzeroIntegerWindow R).card : ℝ) = 2 * (Int.floor R : ℝ) := by
    exact_mod_cast card_nonzeroIntegerWindow hR
  rw [he]
  exact mul_le_mul_of_nonneg_left (Int.floor_le R) (by norm_num)

theorem mem_largePhaseTimes {N R : ℝ} (hN : 0 < N) {k : ℤ} :
    k ∈ largePhaseTimes N R ↔ N / 4 ≤ |(k : ℝ)| ∧ |(k : ℝ)| ≤ R := by
  simp only [largePhaseTimes, Finset.mem_filter, mem_nonzeroIntegerWindow]
  constructor
  · rintro ⟨⟨_, hR⟩, hlo⟩
    exact ⟨hlo, hR⟩
  · rintro ⟨hlo, hR⟩
    refine ⟨⟨?_, hR⟩, hlo⟩
    intro hk
    subst k
    norm_num at hlo
    linarith

theorem card_largePhaseTimes_le {N R : ℝ} (hR : 0 ≤ R) :
    ((largePhaseTimes N R).card : ℝ) ≤ 2 * R := by
  apply le_trans _ (card_nonzeroIntegerWindow_le hR)
  unfold largePhaseTimes
  exact_mod_cast Finset.card_filter_le
    (nonzeroIntegerWindow R) (fun k : ℤ => N / 4 ≤ |(k : ℝ)|)

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PhaseFailureSummability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233.ProductPhases

theorem failureBound_nonneg {m : ℝ} (hm : 0 ≤ m) : 0 ≤ failureBound m := by
  unfold failureBound
  positivity

theorem ten_mul_phaseWidth_le_one {m : ℝ} (hm : 100 ≤ m) :
    10 * m ^ (-19 / 20 : ℝ) ≤ 1 := by
  have hm0 : 0 ≤ m := by linarith
  have hs : (10 : ℝ) ≤ Real.sqrt m := by
    nlinarith [Real.sq_sqrt hm0, Real.sqrt_nonneg m]
  have hb : m ^ (-19 / 20 : ℝ) ≤ (10 : ℝ)⁻¹ := by
    calc
      m ^ (-19 / 20 : ℝ) ≤ m ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (Real.sqrt m)⁻¹ := by rw [Real.rpow_neg hm0, ← Real.sqrt_eq_rpow]
      _ ≤ (10 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs
  nlinarith

theorem failureBound_eq_exp {m : ℝ} (hm : 0 < m) :
    failureBound m = 2 * Real.exp (-(41 / 400 : ℝ) * m * Real.log m +
      (Real.log 2 + (19 / 20 : ℝ) * Real.log 10) * m) := by
  unfold failureBound
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) (Real.rpow_nonneg hm.le _),
    ← Real.rpow_mul hm.le]
  simp only [Real.rpow_def_of_pos hm,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
  rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

theorem eventually_failureBound_le_exp :
    ∀ᶠ m : ℝ in atTop, failureBound m ≤ Real.exp (-m) := by
  let C : ℝ := Real.log 2 + (19 / 20 : ℝ) * Real.log 10
  have hl : ∀ᶠ m : ℝ in atTop,
      (400 / 41 : ℝ) * (C + 2) ≤ Real.log m :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.log 2), hl]
    with m hm hm2 hlog
  rw [failureBound_eq_exp (by linarith)]
  have he : -(41 / 400 : ℝ) * m * Real.log m + C * m ≤ -2 * m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (show 0 ≤ m by linarith)]
  calc
    2 * Real.exp (-(41 / 400 : ℝ) * m * Real.log m + C * m) =
        Real.exp (Real.log 2 + (-(41 / 400 : ℝ) * m * Real.log m + C * m)) := by
      conv_rhs => rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (-m) := Real.exp_le_exp.mpr (by linarith)

theorem summable_failureBound_of_nat_le {m : ℕ → ℝ}
    (hm : ∀ j : ℕ, (j : ℝ) ≤ m j) (hmnonneg : ∀ j, 0 ≤ m j) :
    Summable (fun j => failureBound (m j)) := by
  have hmtop : Tendsto m atTop atTop :=
    tendsto_atTop_mono hm tendsto_natCast_atTop_atTop
  have hb := hmtop.eventually eventually_failureBound_le_exp
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat
  filter_upwards [hb] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg (failureBound_nonneg (hmnonneg j))]
  exact hj.trans (Real.exp_le_exp.mpr (neg_le_neg (hm j)))

theorem summable_failureBound_of_two_pow_le {m : ℕ → ℝ}
    (hm : ∀ j, (2 : ℝ) ^ j ≤ m j) :
    Summable (fun j => failureBound (m j)) := by
  apply summable_failureBound_of_nat_le
  · intro j
    exact le_trans (by exact_mod_cast (show j < 2 ^ j from Nat.lt_two_pow_self).le) (hm j)
  · intro j
    exact le_trans (by positivity) (hm j)

theorem ae_eventually_notMem_of_phase_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (bad : ℕ → Set Ω) {m : ℕ → ℝ}
    (hm : ∀ j, (2 : ℝ) ^ j ≤ m j)
    (hbad : ∀ᶠ j in atTop, μ (bad j) ≤ ENNReal.ofReal (failureBound (m j))) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, ω ∉ bad j := by
  have hs := summable_failureBound_of_two_pow_le hm
  have hreal : Summable (fun j => (μ (bad j)).toReal) := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [hbad] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hnonneg : 0 ≤ failureBound (m j) :=
      failureBound_nonneg (le_trans (by positivity) (hm j))
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hj
    simpa only [ENNReal.toReal_ofReal hnonneg] using hh
  apply MeasureTheory.ae_eventually_notMem
  have ht := hreal.tsum_ofReal_ne_top
  simpa only [ENNReal.ofReal_toReal (measure_ne_top μ _)] using ht

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PhaseRanges
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

theorem threshold_mem_Icc_of_abs_bounds {a x : ℝ}
    (ha : 0 < a) (hlo : a ≤ |x|) (hhi : |x| ≤ 1 / 2) :
    1 - Int.fract x ∈ Set.Icc a (1 - a) := by
  rcases le_or_gt 0 x with hx | hx
  · have habs : |x| = x := abs_of_nonneg hx
    have hfract : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx, by linarith⟩
    rw [hfract]
    constructor <;> linarith
  · have habs : |x| = -x := abs_of_neg hx
    have hfract : Int.fract (-x) = -x :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hnz : Int.fract (-x) ≠ 0 := by rw [hfract]; linarith
    have heq := Int.fract_neg hnz
    simp only [neg_neg] at heq
    rw [heq, hfract]
    constructor <;> linarith

theorem phase_small_window {m K G α k : ℝ}
    (hm : 0 < m) (hK : 0 < K) (hG : 0 < G)
    (hαlo : 1 / (m * K) ≤ α) (hαhi : α ≤ 2 / (m * K))
    (hklo : G * K ≤ |k|) (hkhi : |k| ≤ m * K / 4) :
    1 - Int.fract (k * α) ∈ Set.Icc (G / m) (1 - G / m) := by
  have hmK : 0 < m * K := mul_pos hm hK
  have hα : 0 < α := lt_of_lt_of_le (one_div_pos.mpr hmK) hαlo
  have hlo' : G / m ≤ |k| * α := by
    calc
      G / m = (G * K) * (1 / (m * K)) := by field_simp
      _ ≤ |k| * α := mul_le_mul hklo hαlo (le_of_lt (one_div_pos.mpr hmK))
        (abs_nonneg k)
  have hhi' : |k| * α ≤ 1 / 2 := by
    calc
      |k| * α ≤ (m * K / 4) * (2 / (m * K)) :=
        mul_le_mul hkhi hαhi (le_of_lt hα) (by positivity)
      _ = 1 / 2 := by field_simp <;> ring
  apply threshold_mem_Icc_of_abs_bounds (div_pos hG hm)
  · simpa only [abs_mul, abs_of_pos hα] using hlo'
  · simpa only [abs_mul, abs_of_pos hα] using hhi'

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_LargePhaseAssembly
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductPhases

theorem not_mem_largePhaseFailure_iff {ι : Type*} (J : Finset ι)
    {N : ℝ} (hN : 0 < N) (θ : ι → ℝ) :
    θ ∉ largePhaseFailure J N ↔ largePhaseCondition J N θ := by
  simp only [largePhaseFailure, Set.mem_ofPred_eq, not_exists, not_and,
    not_lt, largePhaseCondition, mem_largePhaseTimes hN]
  constructor
  · intro h k hlo hhi
    exact h k ⟨hlo, hhi⟩
  · intro h k hk
    exact h k hk.1 hk.2

theorem measure_largePhaseFailure_le {ι : Type*}
    (μ : Measure (ι → ℝ)) (J : Finset ι) (N : ℝ) (hm : 100 ≤ (J.card : ℝ))
    (hind : ∀ k : ℤ, iIndepSet
      (fun i => {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
        Set.Icc ((J.card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - (J.card : ℝ) ^ (-19 / 20 : ℝ))}) μ)
    (hmiss : ∀ k ∈ largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card)),
      ∀ i ∈ J, μ {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
        Set.Icc ((J.card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - (J.card : ℝ) ^ (-19 / 20 : ℝ))} ≤
        ENNReal.ofReal (10 * (J.card : ℝ) ^ (-19 / 20 : ℝ))) :
    μ (largePhaseFailure J N) ≤ ENNReal.ofReal (failureBound J.card) := by
  classical
  let m : ℝ := J.card
  let b : ℝ := m ^ (-19 / 20 : ℝ)
  let R : ℝ := m ^ ((4 / 5 : ℝ) * m)
  let q : ℝ := (19 / 20 : ℝ) * m
  let times := largePhaseTimes N R
  let E : ℤ → ι → Set (ι → ℝ) := fun k i =>
    {θ | 1 - Int.fract ((k : ℝ) * θ i) ∉ Set.Icc b (1 - b)}
  have hm0 : 0 ≤ m := by dsimp [m] <;> positivity
  have hb : 0 ≤ b := Real.rpow_nonneg hm0 _
  have hq : 0 ≤ q := by dsimp [q] <;> positivity
  have hp : ENNReal.ofReal (10 * b) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (ten_mul_phaseWidth_le_one hm)
  have hsub : largePhaseFailure J N ⊆
      {θ | ∃ k ∈ times, ∃ t : Finset ι,
        t ⊆ J ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, θ ∈ E k i} := by
    intro θ hθ
    obtain ⟨k, hk, hsmall⟩ := hθ
    obtain ⟨t, ht, hcard, htmiss⟩ :=
      Invariant233.exists_many_misses_of_few_successes J
        (fun i => 1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc b (1 - b)) hsmall
    exact ⟨k, hk, t, ht, hcard.le, htmiss⟩
  have hprob := Invariant233.measure_exists_many_independent_events_le μ E J times
    (fun k _ => hind k) hp hmiss q
  have hnum : (times.card : ℝ) *
      ((2 : ℝ) ^ J.card * (10 * b) ^ q) ≤ failureBound m := by
    calc
      (times.card : ℝ) * ((2 : ℝ) ^ J.card * (10 * b) ^ q) ≤
          (2 * R) * ((2 : ℝ) ^ J.card * (10 * b) ^ q) :=
        mul_le_mul_of_nonneg_right (card_largePhaseTimes_le (Real.rpow_nonneg hm0 _))
          (by positivity)
      _ = failureBound m := by
        dsimp [failureBound, R, b, q, m]
        rw [Real.rpow_natCast]
        ring
  calc
    μ (largePhaseFailure J N) ≤ μ {θ | ∃ k ∈ times, ∃ t : Finset ι,
      t ⊆ J ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, θ ∈ E k i} := measure_mono hsub
    _ ≤ (times.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ J.card *
      ENNReal.ofReal (10 * b) ^ q) := hprob
    _ = ENNReal.ofReal ((times.card : ℝ) * ((2 : ℝ) ^ J.card * (10 * b) ^ q)) := by
      rw [ENNReal.ofReal_mul (p := (times.card : ℝ)) (Nat.cast_nonneg _),
        ENNReal.ofReal_mul (p := (2 : ℝ) ^ J.card) (by positivity),
        ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hq]
      simp
    _ ≤ ENNReal.ofReal (failureBound m) := ENNReal.ofReal_le_ofReal hnum

theorem iIndepSet_phaseMiss_infinitePi {ι : Type*} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (b : ℝ) (k : ℤ) :
    iIndepSet (fun i => {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
      Set.Icc b (1 - b)}) (Measure.infinitePi ν) := by
  have hA : MeasurableSet {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉
      Set.Icc b (1 - b)} := by
    exact ((measurable_const.sub (measurable_const.mul measurable_id).fract)
      measurableSet_Icc).compl
  have hm : ∀ i : ι, MeasurableSet {θ : ι → ℝ |
      1 - Int.fract ((k : ℝ) * θ i) ∉ Set.Icc b (1 - b)} :=
    fun i => hA.preimage (measurable_pi_apply i)
  apply (iIndepSet_iff_meas_biInter hm).mpr
  intro S
  have hi : iIndepFun (fun i (θ : ι → ℝ) => θ i) (Measure.infinitePi ν) :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  exact hi.measure_inter_preimage_eq_mul S (fun _ _ => hA)

theorem infinitePi_phaseMiss_eq {ι : Type*} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (b : ℝ) (k : ℤ) (i : ι) :
    (Measure.infinitePi ν) {θ : ι → ℝ |
      1 - Int.fract ((k : ℝ) * θ i) ∉ Set.Icc b (1 - b)} =
      ν i {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉ Set.Icc b (1 - b)} := by
  have hA : MeasurableSet {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉
      Set.Icc b (1 - b)} := by
    exact ((measurable_const.sub (measurable_const.mul measurable_id).fract)
      measurableSet_Icc).compl
  simpa only [Measure.infinitePi_map_eval, Set.preimage_ofPred_eq] using
    (Measure.map_apply (μ := Measure.infinitePi ν)
      (f := fun θ : ι → ℝ => θ i) (measurable_pi_apply i) hA).symm

theorem ae_largePhaseCondition_of_miss_bounds {ι : Type*}
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (J : ℕ → Finset ι) (N : ℕ → ℝ)
    (hN : ∀ j, 0 < N j) (hgrowth : ∀ j, 2 ^ j ≤ (J j).card)
    (hind : ∀ (j : ℕ) (k : ℤ), iIndepSet
      (fun i => {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
        Set.Icc (((J j).card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - ((J j).card : ℝ) ^ (-19 / 20 : ℝ))}) μ)
    (hmiss : ∀ᶠ j in atTop,
      ∀ k ∈ largePhaseTimes (N j) (((J j).card : ℝ) ^ ((4 / 5 : ℝ) * (J j).card)),
      ∀ i ∈ J j, μ {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
        Set.Icc (((J j).card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - ((J j).card : ℝ) ^ (-19 / 20 : ℝ))} ≤
        ENNReal.ofReal (10 * ((J j).card : ℝ) ^ (-19 / 20 : ℝ))) :
    ∀ᵐ θ ∂μ, ∀ᶠ j in atTop, largePhaseCondition (J j) (N j) θ := by
  have hreal : ∀ j : ℕ, (2 : ℝ) ^ j ≤ ((J j).card : ℝ) := by
    intro j
    exact_mod_cast hgrowth j
  have hindex : ∀ j : ℕ, (j : ℝ) ≤ ((J j).card : ℝ) := by
    intro j
    exact_mod_cast (le_trans (Nat.lt_two_pow_self (n := j)).le (hgrowth j))
  have htop : Tendsto (fun j => ((J j).card : ℝ)) atTop atTop :=
    tendsto_atTop_mono hindex tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ j in atTop, (100 : ℝ) ≤ (J j).card :=
    htop.eventually_ge_atTop 100
  have hbad : ∀ᶠ j in atTop, μ (largePhaseFailure (J j) (N j)) ≤
      ENNReal.ofReal (failureBound (J j).card) := by
    filter_upwards [hlarge, hmiss] with j hj hm
    exact measure_largePhaseFailure_le μ (J j) (N j) hj (hind j) hm
  have hbc := ae_eventually_notMem_of_phase_bound μ
    (fun j => largePhaseFailure (J j) (N j)) hreal hbad
  filter_upwards [hbc] with θ hθ
  filter_upwards [hθ] with j hj
  exact (not_mem_largePhaseFailure_iff (J j) (hN j) θ).mp hj

theorem uniformProduct_ae_largePhaseCondition {ι : Type*}
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (J : ℕ → Finset ι) (N : ℕ → ℝ) (hN : ∀ j, 0 < N j)
    (hgrowth : ∀ j, 2 ^ j ≤ (J j).card)
    (hblock : ∀ j, ∀ i ∈ J j, S i = N j) :
    ∀ᵐ θ ∂Measure.infinitePi
      (fun i => ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
      ∀ᶠ j in atTop, largePhaseCondition (J j) (N j) θ := by
  let ν : ι → Measure ℝ := fun i =>
    ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))
  let (i : ι) : IsProbabilityMeasure (ν i) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) (hS i))
  apply ae_largePhaseCondition_of_miss_bounds (Measure.infinitePi ν) J N hN hgrowth
  · intro j k
    exact iIndepSet_phaseMiss_infinitePi ν _ k
  · apply Filter.Eventually.of_forall
    intro j k hk i hi
    rw [infinitePi_phaseMiss_eq ν _ k i]
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top (ν i) _) (by positivity)).mpr
    change (ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))).real
      {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉
        Set.Icc (((J j).card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - ((J j).card : ℝ) ^ (-19 / 20 : ℝ))} ≤ _
    rw [hblock j i hi]
    exact Invariant233.ModuloIntervalMeasure.uniform_angle_threshold_miss_le
      (hN j) ((mem_largePhaseTimes (hN j)).mp hk).1 (by positivity)

theorem smallPhaseCondition_of_bounds {ι : Type*} (J : Finset ι)
    {K G : ℝ} (hJ : 0 < J.card) (hK : 0 < K) (hG : 0 < G)
    (θ : ι → ℝ)
    (hθ : ∀ i ∈ J, θ i ∈ Set.Icc (1 / ((J.card : ℝ) * K))
      (2 / ((J.card : ℝ) * K))) :
    smallPhaseCondition J K G θ := by
  intro k hklo hkhi i hi
  exact Invariant233.phase_small_window
    (by exact_mod_cast hJ) hK hG (hθ i hi).1 (hθ i hi).2 hklo hkhi

theorem uniformProduct_ae_phaseRanges {ι : Type*} [Countable ι]
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (J : ℕ → Finset ι) (K G : ℕ → ℝ)
    (hK : ∀ j, 0 < K j) (hG : ∀ j, 0 < G j)
    (hgrowth : ∀ j, 2 ^ j ≤ (J j).card)
    (hblock : ∀ j, ∀ i ∈ J j, S i = ((J j).card : ℝ) * K j) :
    ∀ᵐ θ ∂Measure.infinitePi
      (fun i => ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
      (∀ j, smallPhaseCondition (J j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop, largePhaseCondition (J j) (((J j).card : ℝ) * K j) θ) := by
  have hJ : ∀ j, 0 < (J j).card := fun j =>
    lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
  have hN : ∀ j, 0 < ((J j).card : ℝ) * K j := fun j =>
    mul_pos (by exact_mod_cast hJ j) (hK j)
  have hlarge := uniformProduct_ae_largePhaseCondition S hS J
    (fun j => ((J j).card : ℝ) * K j) hN hgrowth hblock
  have hbounds := InvariantProjection.IndependentAngles.intervalProduct_ae_bounds_linearIndependent
    (fun i => 1 / S i) (fun i => 2 / S i)
    (fun i => div_lt_div_of_pos_right (by norm_num) (hS i))
  filter_upwards [hlarge, hbounds] with θ hθlarge hθbounds
  refine ⟨?_, hθlarge⟩
  intro j
  apply smallPhaseCondition_of_bounds (J j) (hJ j) (hK j) (hG j) θ
  intro i hi
  simpa only [hblock j i hi] using hθbounds.1 i

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_BlockPhaseConstruction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Invariant233.ProductPhases

theorem mem_consecutiveBlock_iff (m : ℕ → ℕ) (j i : ℕ) :
    i ∈ consecutiveBlock m j ↔
      (∑ r ∈ Finset.range j, m r) ≤ i ∧
        i < (∑ r ∈ Finset.range j, m r) + m j := by
  simp [consecutiveBlock]

theorem enumeration_block_of_mem (m : ℕ → ℕ)
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    {j i : ℕ} (hi : i ∈ consecutiveBlock m j) : (e i).1 = j := by
  obtain ⟨hlo, hhi⟩ := (mem_consecutiveBlock_iff m j i).mp hi
  let a : Fin (m j) := ⟨i - (∑ r ∈ Finset.range j, m r), by omega⟩
  have ha : e.symm ⟨j, a⟩ = i := by
    rw [he]
    dsimp [a]
    omega
  have heq : e i = ⟨j, a⟩ := by
    rw [← ha, e.apply_symm_apply]
  exact congrArg Sigma.fst heq

theorem mem_consecutiveBlock_enumeration (m : ℕ → ℕ)
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    (i : ℕ) : i ∈ consecutiveBlock m (e i).1 := by
  have hi : i = (∑ r ∈ Finset.range (e i).1, m r) + (e i).2.val := by
    simpa only [e.symm_apply_apply] using he (e i)
  apply (mem_consecutiveBlock_iff m (e i).1 i).mpr
  have hb := (e i).2.isLt
  omega

theorem consecutive_uniformProduct_ae_phaseRanges
    (m : ℕ → ℕ) (hgrowth : ∀ j, 2 ^ j ≤ m j)
    (K G : ℕ → ℝ) (hK : ∀ j, 0 < K j) (hG : ∀ j, 0 < G j)
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Set.Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1)))),
      (∀ j, smallPhaseCondition (consecutiveBlock m j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop,
        largePhaseCondition (consecutiveBlock m j) ((m j : ℝ) * K j) θ) := by
  have hm : ∀ j, 0 < m j := fun j =>
    lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
  have hN : ∀ i : ℕ, 0 < (m (e i).1 : ℝ) * K (e i).1 := fun i =>
    mul_pos (Nat.cast_pos.mpr (hm _)) (hK _)
  have h := uniformProduct_ae_phaseRanges
    (fun i => (m (e i).1 : ℝ) * K (e i).1) hN
    (consecutiveBlock m) K G hK hG
    (by simpa only [card_consecutiveBlock] using hgrowth)
    (by
      intro j i hi
      rw [enumeration_block_of_mem m e he hi, card_consecutiveBlock])
  simpa only [card_consecutiveBlock] using h

theorem exists_consecutive_phase_angles_and
    (m : ℕ → ℕ) (hgrowth : ∀ j, 2 ^ j ≤ m j)
    (K G : ℕ → ℝ) (hK : ∀ j, 0 < K j) (hG : ∀ j, 0 < G j)
    (hsum : Summable (fun j => 1 / K j))
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    {P : (ℕ → ℝ) → Prop}
    (hP : ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Set.Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1)))), P θ) :
    ∃ θ : ℕ → ℝ,
      (∀ j, ∀ i ∈ consecutiveBlock m j,
        θ i ∈ Set.Icc (1 / ((m j : ℝ) * K j)) (2 / ((m j : ℝ) * K j))) ∧
      (∀ i, 0 < θ i) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      LinearIndependent ℚ (fun o : Option ℕ => o.elim 1 θ) ∧
      (∀ j, smallPhaseCondition (consecutiveBlock m j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop,
        largePhaseCondition (consecutiveBlock m j) ((m j : ℝ) * K j) θ) ∧ P θ := by
  have hm : ∀ j, 0 < m j := fun j =>
    lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
  let N : ℕ → ℝ := fun i => (m (e i).1 : ℝ) * K (e i).1
  have hN : ∀ i, 0 < N i := fun i =>
    mul_pos (Nat.cast_pos.mpr (hm _)) (hK _)
  have hblock := InvariantProjection.IndependentAngles.enumerated_block_reciprocal
    m hm K hK hsum e
  have hphase := consecutive_uniformProduct_ae_phaseRanges m hgrowth K G hK hG e he
  obtain ⟨θ, hθ, hsθ, htθ, hiθ, hph, hp⟩ :=
    InvariantProjection.IndependentAngles.exists_prescribed_summable_independent_and
      N hN hblock.1 (hphase.and hP)
  refine ⟨θ, ?_, ?_, hsθ, ?_, hiθ, hph.1, hph.2, hp⟩
  · intro j i hi
    simpa only [N, enumeration_block_of_mem m e he hi] using hθ i
  · intro i
    exact (one_div_pos.mpr (hN i)).trans_le (hθ i).1
  · simpa only [N, hblock.2] using htθ

end Invariant233.ProductPhases

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PhaseBlockWeight
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Invariant233.ProductModel

open ProductPhases

theorem exists_admissible_phase_block_weight_and
    (m : ℕ → ℕ) (hgrowth : ∀ j, 2 ^ j ≤ m j)
    (K G C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hG : ∀ j, 0 < G j)
    (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (hscale : ∀ j, 2 < (m j : ℝ) * K j)
    (hsum : Summable (fun j => 1 / K j))
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    {P : (ℕ → ℝ) → Prop}
    (hP : ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1)))), P θ) :
    ∃ θ : ℕ → ℝ,
      (∀ j, ∀ i ∈ consecutiveBlock m j,
        θ i ∈ Icc (1 / ((m j : ℝ) * K j)) (2 / ((m j : ℝ) * K j))) ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      AdmissibleAnglesAndCosts θ (fun i => C (e i).1) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i => C (e i).1)) ∧
      (∀ᵐ x ∂baseMeasure,
        0 < weight θ (fun i => C (e i).1) x ∧ weight θ (fun i => C (e i).1) x ≤ 1) ∧
      (∀ j, smallPhaseCondition (consecutiveBlock m j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop,
        largePhaseCondition (consecutiveBlock m j) ((m j : ℝ) * K j) θ) ∧ P θ := by
  have hm : ∀ j, 0 < m j := fun j =>
    lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
  have hKpos (j : ℕ) : 0 < K j := zero_lt_one.trans_le (hK j)
  have hCpos (j : ℕ) : 0 < C j := (sq_pos_of_pos (hKpos j)).trans_le (hC j)
  obtain ⟨θ, hθ, hpos, hsθ, htθ, hind, hsmall, hlarge, hp⟩ :=
    exists_consecutive_phase_angles_and m hgrowth K G hKpos hG hsum e he hP
  have hbounds (i : ℕ) : θ i ∈
      Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1)) :=
    hθ (e i).1 i (mem_consecutiveBlock_enumeration m e he i)
  have hunit (i : ℕ) : θ i < 1 :=
    (hbounds i).2.trans_lt ((div_lt_one
      (mul_pos (Nat.cast_pos.mpr (hm _)) (hKpos _))).mpr (hscale _))
  refine ⟨θ, hθ, htθ, ?_, ?_, ?_, hsmall, hlarge, hp⟩
  · exact ⟨fun i => ⟨hpos i, hunit i, hCpos _⟩, hsθ, hind⟩
  · exact hasNegInfiniteLogIntegral_of_block_bounds m hm K C hK hC e θ
      (fun i => ⟨(hpos i).le, hunit i⟩) (fun i => (hbounds i).1)
  · filter_upwards [ae_weight_pos θ (fun i => C (e i).1)
      (fun i => (hpos i).le) (fun i => (hCpos _).le) hsθ] with x hx
    exact ⟨hx, (weight_mem_Icc θ _ x).2⟩

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductDeterminant
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem weightValue_representation_coordinate (θ c : ℕ → ℝ) :
    continuousValueRepresentation θ (weightValue θ c) (measurable_weightValue θ c)
      intervalCoordinate = weightMultiplier θ c := by
  apply multiplier_operator_ext
  intro ξ
  have hleft := continuousValueMultiplier_coordinates_ae θ (weightValue θ c)
    (measurable_weightValue θ c) intervalCoordinate ξ
  have hright : ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      weightMultiplier θ c ξ x k =
        (weight θ c (rotationIterate θ k x) : ℂ) * ξ x k :=
    multiplier_coordinates_ae θ _ _ _ _ _ ξ
  filter_upwards [hleft, hright] with x hl hr
  intro k
  exact (hl k).trans (hr k).symm

theorem weightMultiplier_vectorDeterminant_formula (θ c : ℕ → ℝ) :
    vectorFugledeKadisonDeterminant traceVector (weightMultiplier θ c) =
      ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (weight θ c x ^ 2 + ε.val) ∂baseMeasure) / 2)) := by
  rw [← weightValue_representation_coordinate θ c]
  rw [vectorFugledeKadisonDeterminant_composed_representation baseMeasure
    (weightValue θ c)
    (continuousValueRepresentation θ (weightValue θ c) (measurable_weightValue θ c))
    traceVector (vectorTrace_continuousValueRepresentation θ (weightValue θ c)
      (measurable_weightValue θ c)) intervalCoordinate]
  have hn : ∀ x, ‖intervalCoordinate (weightValue θ c x)‖ = weight θ c x := by
    intro x
    simp only [intervalCoordinate, ContinuousMap.coe_mk, weightValue,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_mem_Icc θ c x).1]
  simp_rw [hn]

theorem weightMultiplier_vectorDeterminant_zero (θ c : ℕ → ℝ)
    (hpos : ∀ᵐ x ∂baseMeasure, 0 < weight θ c x)
    (hinf : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    vectorFugledeKadisonDeterminant traceVector (weightMultiplier θ c) = 0 := by
  rw [weightMultiplier_vectorDeterminant_formula]
  exact ScalarDeterminant.regularized_determinant_eq_zero_of_log_integral
    (measurable_weight θ c) (weight_mem_Icc θ c) hpos hinf

theorem shiftOperator_mem_unitary :
    shiftOperator ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  WeightedShift.fieldShift_mem_unitary 1

theorem weightedOperator_vectorDeterminant_zero_of_ae_pos (θ c : ℕ → ℝ)
    (hpos : ∀ᵐ x ∂baseMeasure, 0 < weight θ c x)
    (hinf : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 := by
  let u : unitary (Hilbert →L[ℂ] Hilbert) := ⟨shiftOperator, shiftOperator_mem_unitary⟩
  change vectorFugledeKadisonDeterminant traceVector
    ((u : Hilbert →L[ℂ] Hilbert) * weightMultiplier θ c) = 0
  rw [vectorFugledeKadisonDeterminant_unitary_mul]
  exact weightMultiplier_vectorDeterminant_zero θ c hpos hinf

theorem weightedOperator_vectorDeterminant_zero (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hinf : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 :=
  weightedOperator_vectorDeterminant_zero_of_ae_pos θ c
    (ae_weight_pos θ c hθ0 hc hθ) hinf

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductRealizationAssembly
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Invariant233.ProductModel

theorem product_realization_of_ae_sampling_oai
    (hsampling : ∀ (p : ProductScaleData) (_hp : ProductScaleLaws p)
      (S : ℕ → ℝ) (_hS : ∀ i, 0 < S i)
      (_hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
        S i = (p.m j : ℝ) * p.K j),
      ∀ᵐ θ ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
        HasAllFiniteCoordinateSampling θ) :
    ∃ θ c : ℕ → ℝ, AdmissibleAnglesAndCosts θ c ∧
      HasAllFiniteCoordinateSampling θ ∧
      (∀ᵐ x ∂baseMeasure, 0 < weight θ c x) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ c) ∧
      IsTypeII1FactorWithVector (factor θ) traceVector ∧
      HasSeparablePredual (factor θ) ∧
      weightedOperator θ c ∈ factor θ ∧ weightedOperator θ c ≠ 0 ∧
      NormQuasinilpotent (weightedOperator θ c) ∧
      vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 ∧
      spectrum ℂ (weightedOperator θ c) = {0} ∧
      IsVectorBrownMeasure traceVector (weightedOperator θ c) (Measure.dirac 0) ∧
      HasOnlyTrivialInvariantProjections (factor θ) (weightedOperator θ c) ∧
      ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  obtain ⟨p, hp⟩ := ProductScaleConstruction.exists_product_scales
  have hm (j : ℕ) : 0 < p.m j := lt_of_lt_of_le (by norm_num) (hp.m_ge_100 j)
  obtain ⟨e, he⟩ := InvariantProjection.IndependentAngles.exists_consecutiveBlocks_equiv p.m hm
  have hK (j : ℕ) : (1 : ℝ) ≤ p.K j := by exact_mod_cast hp.K_pos j
  have hG (j : ℕ) : (0 : ℝ) < p.G j := by exact_mod_cast hp.G_pos j
  have hC (j : ℕ) : (p.K j : ℝ) ^ 2 ≤ p.C j := by
    rw [hp.C_eq j]
    exact le_max_right _ _
  have hscale (j : ℕ) : (2 : ℝ) < (p.m j : ℝ) * p.K j := by
    have hm100 : (100 : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_100 j
    have hk := hK j
    nlinarith
  have hS (i : ℕ) : 0 < (p.m (e i).1 : ℝ) * p.K (e i).1 :=
    mul_pos (Nat.cast_pos.mpr (hm _)) (Nat.cast_pos.mpr (hp.K_pos _))
  have hsamp := hsampling p hp
    (fun i => (p.m (e i).1 : ℝ) * p.K (e i).1) hS
    (by
      intro j i hi
      rw [ProductPhases.enumeration_block_of_mem p.m e he hi])
  obtain ⟨θ, hθ, _hsum, hadm, hlog, hpos, hsmall, hlarge, hs⟩ :=
    exists_admissible_phase_block_weight_and p.m hp.m_ge_pow_self
      (fun j => (p.K j : ℝ)) (fun j => (p.G j : ℝ)) p.C
      hK hG hC hscale hp.summable_reciprocal e he hsamp
  have hθ0 (i : ℕ) : 0 ≤ θ i := (hadm.1 i).1.le
  have hθ01 (i : ℕ) : θ i ∈ Ico (0 : ℝ) 1 := ⟨hθ0 i, (hadm.1 i).2.1⟩
  have hc (i : ℕ) : 0 ≤ p.C (e i).1 := (hadm.1 i).2.2.le
  have hdiv := (hasNegInfiniteLogIntegral_iff_tsum θ _ hθ01 hc).mp hlog
  obtain ⟨hfactor, hpredual, _hfields, _htrace⟩ := factor_complete θ hadm.2.2
  refine ⟨θ, (fun i => p.C (e i).1), hadm, hs,
    hpos.mono (fun _ hx => hx.1), hlog, hfactor, hpredual,
    weightedOperator_mem_factor θ _,
    weightedOperator_ne_zero θ _ hθ0 hc hadm.2.1,
    weightedOperator_normQuasinilpotent θ _ hθ0 hc hadm.2.1 hdiv,
    weightedOperator_vectorDeterminant_zero θ _ hθ0 hc hadm.2.1 hlog,
    weightedOperator_spectrum_eq_singleton_zero θ _ hθ0 hc hadm.2.1 hdiv,
    weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral
      θ _ hθ01 hc hadm.2.1 hlog,
    ?_, productPolarStructure_of_admissible θ _ hadm⟩
  exact hasOnlyTrivialInvariantProjections_of_sampling_and_phases hp e he θ hadm
    hθ hsmall hlarge hs

end Invariant233.ProductModel

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.product_realization_of_ae_sampling_oai := @OAI.Invariant233.ProductModel.product_realization_of_ae_sampling_oai
