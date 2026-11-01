-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.integral_discountedDynkinProcess_stoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:20:00.543979+00:00
-- url     : https://prove2.me/submissions/fe6f7241-aed4-491e-b657-6af4e9eddd25

import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuous_discountedDynkinProcess
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_integral_discountedDynkinProcess
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_martingale_discountedDynkinProcess
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_norm_discountedDynkinProcess_le
import Theorems.Thm_MarkovProcess_integral_stoppedValue_le_of_locallyBounded

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Optional stopping in continuous time, at a bounded finite stopping time

Mathlib's optional stopping theorem is discrete-time.  This file proves the continuous-time
statement the library consumes: if `M` is a real-valued martingale for a filtration indexed by
`ℝ≥0`, bounded on bounded time intervals and right continuous in time along every sample point,
and `T` is a finite stopping time bounded by a deterministic horizon `K`, then

  `∫ omega, M (T omega) omega ∂mu = ∫ omega, M 0 omega ∂mu`

(`integral_stoppedValue_eq_of_locallyBounded`, with the uniformly bounded case
`integral_stoppedValue_eq_of_le`).

For a supermartingale the corresponding expectation is at most its initial expectation
(`integral_stoppedValue_le_of_locallyBounded` and `integral_stoppedValue_le_of_le`).

The proof samples a supermartingale on the dyadic grid and applies Mathlib's
`Submartingale.expected_stoppedValue_mono` after negation.  The dyadic ceilings `T_n` of a finite
stopping time are stopping times with finite range that decrease to `T`
(`Path/StoppingTimeDyadicCeiling.lean`), so dominated convergence and right continuity give the
supermartingale inequality.  Applying that inequality to a martingale and its negation gives the
martingale equality.

Nothing here is specific to path space: the statements are for an arbitrary measurable space with
a filtration indexed by `ℝ≥0`.  No optional-stopping result for unbounded stopping times is
asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section

variable {Omega : Type*} {m : MeasurableSpace Omega} {mu : Measure Omega}
  {ℱ : Filtration NNReal m} {M : NNReal → Omega → ℝ}

section FiniteRange

variable [IsFiniteMeasure mu]









end FiniteRange

section DyadicApproximation













end DyadicApproximation

section OptionalStopping

variable [IsFiniteMeasure mu]





/-- **Optional stopping at a bounded finite stopping time**, for a martingale that is bounded on
bounded time intervals and right continuous in time.

This is obtained by applying the supermartingale inequality to `M` and `-M`. -/
theorem integral_stoppedValue_eq_of_locallyBounded (hM : Martingale M ℱ mu)
    (hbound : ∀ v : NNReal, ∃ C : ℝ, ∀ t ≤ v, ∀ omega, ‖M t omega‖ ≤ C)
    (hright : ∀ (omega : Omega) (v : NNReal),
      ContinuousWithinAt (fun t : NNReal ↦ M t omega) (Set.Ici v) v)
    {T : Omega → NNReal}
    (hT : IsStoppingTime ℱ fun omega ↦ ((T omega : NNReal) : WithTop NNReal))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) :
    ∫ omega, M (T omega) omega ∂mu = ∫ omega, M 0 omega ∂mu := by
  apply le_antisymm
  · exact integral_stoppedValue_le_of_locallyBounded hM.supermartingale hbound hright hT hTK
  · have hnegBound : ∀ v : NNReal, ∃ C : ℝ, ∀ t ≤ v, ∀ omega, ‖-M t omega‖ ≤ C := by
      intro v
      obtain ⟨C, hC⟩ := hbound v
      exact ⟨C, fun t ht omega ↦ by simpa only [norm_neg] using hC t ht omega⟩
    have hneg := integral_stoppedValue_le_of_locallyBounded hM.neg.supermartingale
      hnegBound (fun omega v ↦ (hright omega v).neg) hT hTK
    simpa only [Pi.neg_apply, integral_neg, neg_le_neg_iff] using hneg



end OptionalStopping

end

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The discounted Dynkin formula

For the continuous-path process of a conservative Feller semigroup, this file proves that the
Dynkin process with exponential discount is a martingale and applies optional stopping at an exit
time truncated by a deterministic horizon.  At zero discount it agrees with the Dynkin process
of `Trajectory/DynkinMartingale.lean`.

Main results: `IsFellerKernelSemigroup.discountedDynkinProcess`,
`discountedDynkinProcess_apply`, `discountedDynkinProcess_zero`,
`norm_discountedDynkinProcess_le`, `continuous_discountedDynkinProcess`,
`stronglyMeasurable_integral_discountedGenerator`,
`stronglyMeasurable_discountedDynkinProcess_canonicalFiltration`,
`stronglyMeasurable_discountedDynkinProcess`, `adapted_discountedDynkinProcess`,
`integrable_discountedDynkinProcess`, `integral_discountedDynkinProcess`,
`discountedDynkinProcess_eq_add_shift`, `martingale_discountedDynkinProcess`,
`progMeasurable_discountedDynkinProcess`, `measurable_discountedDynkinProcess_stoppingTime`,
`integral_discountedDynkinProcess_stoppingTime`, and
`integral_exp_eval_exitTimeTrunc_sub_eq_integral_integral`.

No assertion is made at an unbounded stopping time or about passage to an infinite horizon.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section ProcessDefinition













end ProcessDefinition

section Adapted

variable [SecondCountableTopology alpha]











end Adapted

section Expectation

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)





end Expectation

section Decomposition



end Decomposition

section Martingale

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)



end Martingale

section OptionalStopping

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)









end OptionalStopping

end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The discounted Dynkin formula

For the continuous-path process of a conservative Feller semigroup, this file proves that the
Dynkin process with exponential discount is a martingale and applies optional stopping at an exit
time truncated by a deterministic horizon.  At zero discount it agrees with the Dynkin process
of `Trajectory/DynkinMartingale.lean`.

Main results: `IsFellerKernelSemigroup.discountedDynkinProcess`,
`discountedDynkinProcess_apply`, `discountedDynkinProcess_zero`,
`norm_discountedDynkinProcess_le`, `continuous_discountedDynkinProcess`,
`stronglyMeasurable_integral_discountedGenerator`,
`stronglyMeasurable_discountedDynkinProcess_canonicalFiltration`,
`stronglyMeasurable_discountedDynkinProcess`, `adapted_discountedDynkinProcess`,
`integrable_discountedDynkinProcess`, `integral_discountedDynkinProcess`,
`discountedDynkinProcess_eq_add_shift`, `martingale_discountedDynkinProcess`,
`progMeasurable_discountedDynkinProcess`, `measurable_discountedDynkinProcess_stoppingTime`,
`integral_discountedDynkinProcess_stoppingTime`, and
`integral_exp_eval_exitTimeTrunc_sub_eq_integral_integral`.

No assertion is made at an unbounded stopping time or about passage to an infinite horizon.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}







variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)





namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (lam : ℝ)
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) (x : alpha) :
    ∫ omega, hFeller.discountedDynkinProcess f lam (T omega) omega
        ∂(IsConservative.continuousProcess P hP x) =
      (f : C₀(alpha, ℝ)) x := by
  let g : C₀(alpha, ℝ) :=
    hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))
  have hbound : ∀ v : NNReal, ∃ C : ℝ, ∀ t ≤ v, ∀ omega : ContinuousPath alpha,
      ‖hFeller.discountedDynkinProcess f lam t omega‖ ≤ C := by
    intro v
    refine ⟨Real.exp (|lam| * (v : ℝ)) *
      (‖(f : C₀(alpha, ℝ))‖ + (v : ℝ) * ‖g‖), fun t ht omega ↦
        (hFeller.norm_discountedDynkinProcess_le f lam t omega).trans ?_⟩
    have hexp : Real.exp (|lam| * (t : ℝ)) ≤ Real.exp (|lam| * (v : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) (abs_nonneg lam)
    have hinside : ‖(f : C₀(alpha, ℝ))‖ + (t : ℝ) * ‖g‖ ≤
        ‖(f : C₀(alpha, ℝ))‖ + (v : ℝ) * ‖g‖ :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
        (NNReal.coe_le_coe.mpr ht) (norm_nonneg g))
    exact mul_le_mul hexp hinside
      (add_nonneg (norm_nonneg _) (mul_nonneg t.coe_nonneg (norm_nonneg g)))
      (Real.exp_pos _).le
  have hright : ∀ (omega : ContinuousPath alpha) (v : NNReal),
      ContinuousWithinAt (fun t : NNReal ↦ hFeller.discountedDynkinProcess f lam t omega)
        (Set.Ici v) v :=
    fun omega _ ↦ (hFeller.continuous_discountedDynkinProcess f lam omega).continuousWithinAt
  rw [MarkovProcess.integral_stoppedValue_eq_of_locallyBounded
    (hFeller.martingale_discountedDynkinProcess hP hK f lam x) hbound hright hT hTK]
  exact hFeller.integral_discountedDynkinProcess hP hK f lam 0 x
