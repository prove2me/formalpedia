-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.kernelResolvent_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:21:54.149675+00:00
-- url     : https://prove2.me/submissions/2fb61036-3ed6-4d4e-b3ab-60c31c7382b1

import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacResolvent_ed9736ae
import Definitions.Def_MarkovProcess_V3H_Trajectory_ResolventExitDecomposition_db489119
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
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
# Feynman--Kac resolvents

This file Laplace-transforms the nonnegative extended-real Feynman--Kac operators and proves their
path-occupation formula, comparison with killed resolvents, and perturbation identities against
the unperturbed kernel resolvent.

Main results: `IsConservative.feynmanKacResolvent`,
`IsConservative.feynmanKacResolvent_eq_lintegral_path`,
`IsConservative.killedResolvent_le_feynmanKacResolvent`,
`IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le`,
`IsFellerKernelSemigroup.kernelResolvent_eq_feynmanKacResolvent_add`, and
`IsFellerKernelSemigroup.feynmanKacResolvent_eq_kernelResolvent_sub`.

No uniqueness statement for the associated resolvent equation is asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

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
# Feynman--Kac resolvents

This file Laplace-transforms the nonnegative extended-real Feynman--Kac operators and proves their
path-occupation formula, comparison with killed resolvents, and perturbation identities against
the unperturbed kernel resolvent.

Main results: `IsConservative.feynmanKacResolvent`,
`IsConservative.feynmanKacResolvent_eq_lintegral_path`,
`IsConservative.killedResolvent_le_feynmanKacResolvent`,
`IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le`,
`IsFellerKernelSemigroup.kernelResolvent_eq_feynmanKacResolvent_add`, and
`IsFellerKernelSemigroup.feynmanKacResolvent_eq_kernelResolvent_sub`.

No uniqueness statement for the associated resolvent equation is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



















open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
omit [MetricSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
theorem solution (hP : P.IsConservative) (lam : ℝ) (hlam : 0 < lam)
    {f : alpha → ℝ≥0∞} {D : NNReal} (hfD : ∀ y, f y ≤ (D : ℝ≥0∞)) (x : alpha) :
    P.kernelResolvent lam f x < ∞ := by
  have hinner (t : ℝ) : (∫⁻ y, f y ∂(P (Real.toNNReal t) x)) ≤ (D : ℝ≥0∞) := by
    let hMarkovT : IsMarkovKernel (P (Real.toNNReal t)) :=
      hP.isMarkovKernel (Real.toNNReal t)
    calc
      (∫⁻ y, f y ∂(P (Real.toNNReal t) x)) ≤ ∫⁻ _y, (D : ℝ≥0∞)
          ∂(P (Real.toNNReal t) x) := lintegral_mono hfD
      _ = D := by simp only [lintegral_const, measure_univ, mul_one]
  have hweightInt : IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) * (D : ℝ))
      (Ioi (0 : ℝ)) := by
    exact (integrableOn_exp_mul_Ioi (show -lam < 0 by linarith only [hlam]) 0).mul_const D
  unfold SubMarkovKernelSemigroup.kernelResolvent
  calc
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        ∫⁻ y, f y ∂(P (Real.toNNReal t) x)) ≤
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t) * (D : ℝ)) := by
      apply setLIntegral_mono'
      · exact measurableSet_Ioi
      · intro t _ht
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
          show ENNReal.ofReal (D : ℝ) = (D : ℝ≥0∞) by simp only [ENNReal.ofReal_coe_nnreal]]
        exact mul_le_mul_of_nonneg_left (hinner t) bot_le
    _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * (D : ℝ)) := by
      exact (ofReal_integral_eq_lintegral_ofReal hweightInt
        (Eventually.of_forall fun t ↦ mul_nonneg (Real.exp_pos _).le D.coe_nonneg)).symm
    _ < ∞ := ENNReal.ofReal_lt_top
