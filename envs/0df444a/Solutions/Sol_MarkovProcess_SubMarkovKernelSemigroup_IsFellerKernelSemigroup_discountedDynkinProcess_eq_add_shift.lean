-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.discountedDynkinProcess_eq_add_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:35:29.486871+00:00
-- url     : https://prove2.me/submissions/090dd1c4-16d4-4770-bc45-9530a53fd8ea

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section ProcessDefinition



/-- The discounted Dynkin process, unfolded. -/
theorem IsFellerKernelSemigroup.discountedDynkinProcess_apply
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) (omega : ContinuousPath alpha) :
    hFeller.discountedDynkinProcess f lam t omega =
      Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t) -
        ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) *
          (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
            (omega (Real.toNNReal s)) :=
  rfl









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





namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (s t : NNReal) (hst : s ≤ t) (omega : ContinuousPath alpha) :
    hFeller.discountedDynkinProcess f lam t omega =
      hFeller.discountedDynkinProcess f lam s omega -
        Real.exp (-lam * (s : ℝ)) * (f : C₀(alpha, ℝ)) (omega s) +
        Real.exp (-lam * (s : ℝ)) *
          hFeller.discountedDynkinProcess f lam (t - s) (ContinuousPath.shift s omega) := by
  let g : C₀(alpha, ℝ) :=
    hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))
  let q : ℝ → ℝ := fun v ↦ Real.exp (-lam * v) * g (omega (Real.toNNReal v))
  have hscaledTail : Real.exp (-lam * (s : ℝ)) *
        (∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ), Real.exp (-lam * u) *
          g (omega (s + Real.toNNReal u))) =
      ∫ v in (s : ℝ)..(t : ℝ), q v := by
    rw [← intervalIntegral.integral_const_mul]
    have hcongr : (∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ),
          Real.exp (-lam * (s : ℝ)) *
            (Real.exp (-lam * u) * g (omega (s + Real.toNNReal u)))) =
        ∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ), q (u + s) := by
      refine intervalIntegral.integral_congr fun u hu ↦ ?_
      have hu0 : (0 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (t - s : NNReal).coe_nonneg] at hu
        exact hu.1
      have hcoe : Real.toNNReal (u + s) = s + Real.toNNReal u := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, Real.coe_toNNReal u hu0,
          Real.coe_toNNReal _ (add_nonneg hu0 s.coe_nonneg)]
        ring
      dsimp only [q]
      rw [hcoe, ← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [hcongr, intervalIntegral.integral_comp_add_right q (s : ℝ), zero_add]
    congr 1
    rw [NNReal.coe_sub hst]
    ring
  have hcont : Continuous q :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (g.continuous.comp (omega.continuous.comp continuous_real_toNNReal))
  have hsplit : (∫ v in (0 : ℝ)..(s : ℝ), q v) +
      (∫ v in (s : ℝ)..(t : ℝ), q v) = ∫ v in (0 : ℝ)..(t : ℝ), q v :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hExp : Real.exp (-lam * (t : ℝ)) =
      Real.exp (-lam * (s : ℝ)) * Real.exp (-lam * ((t - s : NNReal) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    rw [NNReal.coe_sub hst]
    ring
  simp only [IsFellerKernelSemigroup.discountedDynkinProcess_apply,
    ContinuousPath.shift_apply, add_tsub_cancel_of_le hst]
  change _ - ∫ v in (0 : ℝ)..(t : ℝ), q v =
    (_ - ∫ v in (0 : ℝ)..(s : ℝ), q v) - _ +
      Real.exp (-lam * (s : ℝ)) *
        (_ - ∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ),
          Real.exp (-lam * u) * g (omega (s + Real.toNNReal u)))
  rw [hExp, mul_assoc, mul_sub, hscaledTail]
  linarith only [hsplit]
