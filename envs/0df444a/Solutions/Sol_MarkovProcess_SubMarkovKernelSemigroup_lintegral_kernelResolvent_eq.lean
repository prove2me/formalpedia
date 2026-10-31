-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.lintegral_kernelResolvent_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:44:20.358037+00:00
-- url     : https://prove2.me/submissions/42998704-e8b7-4bf0-800c-1c19592e8221

import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Definitions.Def_MarkovProcess_V3H_Killed_GluingResolventEquation_b19dddc8
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
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
# The resolvent equation for a kernel resolvent

The kernel resolvent of a sub-Markov kernel semigroup satisfies the resolvent equation

  `R_lam f = R_mu f + (mu - lam) R_lam (R_mu f)`   for `0 < lam < mu`

(`SubMarkovKernelSemigroup.kernelResolvent_resolventEquation`), as an identity of
extended-nonnegative-real valued observables, so no integrability hypothesis is needed.  The proof
is the convolution identity for exponential weights

  `e^{-mu u} + (mu - lam) ∫_0^u e^{-lam s} e^{-mu (u - s)} ds = e^{-lam u}`

(`expWeight_convolution`) together with the Chapman--Kolmogorov law, which turns the composition
of the two resolvents into a convolution in time.

Main definitions: `expWeight`.

The same double-integral form is symmetric in the two shifts, so the two resolvents commute
(`SubMarkovKernelSemigroup.kernelResolvent_comm`).

Main results: `expWeight_convolution`,
`SubMarkovKernelSemigroup.kernelResolvent_eq_lintegral_expWeight`,
`SubMarkovKernelSemigroup.kernelResolvent_comp_eq_lintegral`,
`SubMarkovKernelSemigroup.kernelResolvent_comm`,
`SubMarkovKernelSemigroup.kernelResolvent_resolventEquation`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess













namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha] (P : SubMarkovKernelSemigroup alpha)

















end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The resolvent equation for a kernel resolvent

The kernel resolvent of a sub-Markov kernel semigroup satisfies the resolvent equation

  `R_lam f = R_mu f + (mu - lam) R_lam (R_mu f)`   for `0 < lam < mu`

(`SubMarkovKernelSemigroup.kernelResolvent_resolventEquation`), as an identity of
extended-nonnegative-real valued observables, so no integrability hypothesis is needed.  The proof
is the convolution identity for exponential weights

  `e^{-mu u} + (mu - lam) ∫_0^u e^{-lam s} e^{-mu (u - s)} ds = e^{-lam u}`

(`expWeight_convolution`) together with the Chapman--Kolmogorov law, which turns the composition
of the two resolvents into a convolution in time.

Main definitions: `expWeight`.

The same double-integral form is symmetric in the two shifts, so the two resolvents commute
(`SubMarkovKernelSemigroup.kernelResolvent_comm`).

Main results: `expWeight_convolution`,
`SubMarkovKernelSemigroup.kernelResolvent_eq_lintegral_expWeight`,
`SubMarkovKernelSemigroup.kernelResolvent_comp_eq_lintegral`,
`SubMarkovKernelSemigroup.kernelResolvent_comm`,
`SubMarkovKernelSemigroup.kernelResolvent_resolventEquation`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
















variable {alpha : Type*} [MeasurableSpace alpha] (P : SubMarkovKernelSemigroup alpha)









namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution (mu : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, P.kernelResolvent mu f y ∂P (Real.toNNReal s) x =
      ∫⁻ t, expWeight mu t * P.transitionProfile f x (s + t) := by
  have := P.isFiniteMeasure_apply (Real.toNNReal s) x
  have hjoint : Measurable fun q : alpha × ℝ ↦
      expWeight mu q.2 * ∫⁻ z, f z ∂P (Real.toNNReal q.2) q.1 :=
    ((measurable_expWeight mu).comp measurable_snd).mul
      ((Measure.measurable_lintegral hf).comp
        (P.measurable_toMeasure.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk
          measurable_fst)))
  calc ∫⁻ y, P.kernelResolvent mu f y ∂P (Real.toNNReal s) x
      = ∫⁻ y, (∫⁻ t, expWeight mu t * ∫⁻ z, f z ∂P (Real.toNNReal t) y)
          ∂P (Real.toNNReal s) x :=
        lintegral_congr fun y ↦ P.kernelResolvent_eq_lintegral_expWeight mu f y
    _ = ∫⁻ t, ∫⁻ y, expWeight mu t * (∫⁻ z, f z ∂P (Real.toNNReal t) y)
          ∂P (Real.toNNReal s) x := lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ t, expWeight mu t * ∫⁻ y, (∫⁻ z, f z ∂P (Real.toNNReal t) y)
          ∂P (Real.toNNReal s) x :=
        lintegral_congr fun t ↦ lintegral_const_mul _
          ((Measure.measurable_lintegral hf).comp
            (P.measurable_toMeasure.comp (measurable_const.prodMk measurable_id)))
    _ = ∫⁻ t, expWeight mu t * P.transitionProfile f x (s + t) := by
        refine lintegral_congr fun t ↦ ?_
        rcases le_or_gt t 0 with ht | ht
        · rw [expWeight_of_nonpos ht, zero_mul, zero_mul]
        · rw [transitionProfile, Real.toNNReal_add hs.le ht.le, P.lintegral_add _ _ x hf]
