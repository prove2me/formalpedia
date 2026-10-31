-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional_joint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:47:02.219869+00:00
-- url     : https://prove2.me/submissions/dea6cca4-282c-4bf2-ae68-5092d3d068be

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exp
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Prod
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
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feynman--Kac functionals and semigroups

For the continuous-path process of a conservative Feller semigroup, this file constructs the
Feynman--Kac operators associated with a bounded nonnegative measurable potential.  It proves
measurability and bounds for the accumulated potential and operators, the identity at time zero,
and the Feynman--Kac semigroup law.

Main results: `feynmanKacAdditiveFunctional`,
`stronglyMeasurable_feynmanKacAdditiveFunctional`,
`continuous_feynmanKacAdditiveFunctional`, `feynmanKacAdditiveFunctional_add`,
`IsConservative.feynmanKac`, `IsConservative.feynmanKac_zero`,
`IsConservative.measurable_feynmanKac`, `IsConservative.feynmanKac_nonneg`,
`IsConservative.feynmanKac_le`, `IsConservative.feynmanKac_add_apply`,
`IsConservative.feynmanKac_smul_apply`, and `IsFellerKernelSemigroup.feynmanKac_add`.

The resolvent and perturbation identities are developed in `Trajectory/FeynmanKacResolvent.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]



omit [MeasurableSpace alpha] [BorelSpace alpha] in
/-- The accumulated potential is unfolded as its path integral. -/
theorem feynmanKacAdditiveFunctional_apply (q : alpha → ℝ) (t : NNReal)
    (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q t omega =
      ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) :=
  rfl

variable [SecondCountableTopology alpha]























variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)






































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
# Feynman--Kac functionals and semigroups

For the continuous-path process of a conservative Feller semigroup, this file constructs the
Feynman--Kac operators associated with a bounded nonnegative measurable potential.  It proves
measurability and bounds for the accumulated potential and operators, the identity at time zero,
and the Feynman--Kac semigroup law.

Main results: `feynmanKacAdditiveFunctional`,
`stronglyMeasurable_feynmanKacAdditiveFunctional`,
`continuous_feynmanKacAdditiveFunctional`, `feynmanKacAdditiveFunctional_add`,
`IsConservative.feynmanKac`, `IsConservative.feynmanKac_zero`,
`IsConservative.measurable_feynmanKac`, `IsConservative.feynmanKac_nonneg`,
`IsConservative.feynmanKac_le`, `IsConservative.feynmanKac_add_apply`,
`IsConservative.feynmanKac_smul_apply`, and `IsFellerKernelSemigroup.feynmanKac_add`.

The resolvent and perturbation identities are developed in `Trajectory/FeynmanKacResolvent.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]





variable [SecondCountableTopology alpha]





namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution {q : alpha → ℝ}
    (hq : Measurable q) :
    StronglyMeasurable fun p : NNReal × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q p.1 p.2 := by
  let phi : (NNReal × ContinuousPath alpha) × ℝ → ℝ := fun p ↦
    if 0 < p.2 ∧ p.2 ≤ (p.1.1 : ℝ)
    then q (p.1.2 (Real.toNNReal p.2)) else 0
  have hset : MeasurableSet {p : (NNReal × ContinuousPath alpha) × ℝ |
      0 < p.2 ∧ p.2 ≤ (p.1.1 : ℝ)} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd
        (NNReal.continuous_coe.measurable.comp (measurable_fst.comp measurable_fst)))
  have heval : Measurable fun p : (NNReal × ContinuousPath alpha) × ℝ ↦
      q (p.1.2 (Real.toNNReal p.2)) := by
    have hpath : Measurable fun p : (NNReal × ContinuousPath alpha) × ℝ ↦
        p.1.2 (Real.toNNReal p.2) :=
      (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk
          (measurable_snd.comp measurable_fst))
    exact hq.comp hpath
  have hphi : StronglyMeasurable phi := by
    exact (heval.ite hset measurable_const).stronglyMeasurable
  have hint : StronglyMeasurable fun p : NNReal × ContinuousPath alpha ↦
      ∫ s, phi (p, s) := hphi.integral_prod_right'
  have heq : (fun p : NNReal × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q p.1 p.2) = fun p ↦ ∫ s, phi (p, s) := by
    funext p
    rw [feynmanKacAdditiveFunctional_apply,
      intervalIntegral.integral_of_le p.1.coe_nonneg]
    change (∫ s in Ioc (0 : ℝ) (p.1 : ℝ), q (p.2 (Real.toNNReal s))) =
      ∫ s, phi (p, s)
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact Eventually.of_forall fun s ↦ by
      by_cases hs : s ∈ Ioc (0 : ℝ) (p.1 : ℝ)
      · have hs' : 0 < s ∧ s ≤ (p.1 : ℝ) := hs
        simp only [indicator_of_mem hs, phi, if_pos hs']
      · have hs' : ¬(0 < s ∧ s ≤ (p.1 : ℝ)) := hs
        simp only [indicator_of_notMem hs, phi, if_neg hs']
  rw [heq]
  exact hint
