-- Prove2me | solution 1 for MarkovProcess.PositiveC0ContractiveResolvent.OnePointRegular.ae_exitTime_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:50:57.720726+00:00
-- url     : https://prove2.me/submissions/329d5583-3968-498d-b063-8b137e22458a

import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
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
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_lintegral_exp_neg_onePoint_exitTime

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A conservative resolvent keeps the compactified process in the live space

The Laplace transform of the finite exit time from the live part of the compactification is one
minus the shift times the kernel resolvent of the constant observable one
(`Kernel/OnePointKilled.lean`).  When that product is one, the transform vanishes, so the exit
time is almost surely infinite: the compactified process started at a live point almost surely
never reaches the added point
(`PositiveC0ContractiveResolvent.OnePointRegular.ae_exitTime_eq_top`).  No kernel into the
continuous paths of the live space is produced here; the statement is about the law of the
compactified process.

The regularity data of the compactification are an explicit hypothesis, as everywhere the
continuous-path process is formed.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {R : PositiveC0ContractiveResolvent X}



end MarkovProcess.PositiveC0ContractiveResolvent


open MarkovProcess
open MarkovProcess.PositiveC0ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A conservative resolvent keeps the compactified process in the live space

The Laplace transform of the finite exit time from the live part of the compactification is one
minus the shift times the kernel resolvent of the constant observable one
(`Kernel/OnePointKilled.lean`).  When that product is one, the transform vanishes, so the exit
time is almost surely infinite: the compactified process started at a live point almost surely
never reaches the added point
(`PositiveC0ContractiveResolvent.OnePointRegular.ae_exitTime_eq_top`).  No kernel into the
continuous paths of the live space is produced here; the statement is about the law of the
compactified process.

The regularity data of the compactification are an explicit hypothesis, as everywhere the
continuous-path process is formed.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty



open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {R : PositiveC0ContractiveResolvent X}

namespace MarkovProcess.PositiveC0ContractiveResolvent.OnePointRegular

end MarkovProcess.PositiveC0ContractiveResolvent.OnePointRegular
open MarkovProcess.PositiveC0ContractiveResolvent.OnePointRegular
theorem solution (h : R.OnePointRegular) {lam : ℝ} (hlam : 0 < lam)
    (x : X) (hone : ENNReal.ofReal lam *
      R.kernelSemigroup.kernelResolvent lam (fun _ : X ↦ 1) x = 1) :
    letI := h.metricSpace
    letI := h.completeSpace
    ∀ᵐ omega ∂IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup (x : OnePoint X),
      ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega = ⊤ := by
  let := h.metricSpace
  let := h.completeSpace
  have hlaplace := R.lintegral_exp_neg_onePoint_exitTime h.rho h.continuous_rho h.rho_pos
    h.lipschitz_rho h.isCompact_superlevel h.kolmogorovRegular lam hlam x
  rw [hone, tsub_self] at hlaplace
  have hmeasTime : Measurable
      (ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) :
        ContinuousPath (OnePoint X) → ℝ≥0∞) :=
    ContinuousPath.measurable_exitTime _ OnePoint.isOpen_range_coe
  have hmeasSet : MeasurableSet
      {omega : ContinuousPath (OnePoint X) |
        ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega < ⊤} :=
    measurableSet_lt hmeasTime measurable_const
  have hmeas : Measurable
      (({omega : ContinuousPath (OnePoint X) |
          ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega < ⊤}).indicator
        (fun omega ↦ ENNReal.ofReal (Real.exp (-lam *
          (ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega).toReal)))) :=
    Measurable.indicator
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
        ((measurable_const.mul hmeasTime.ennreal_toReal))))
      hmeasSet
  have hzero := (lintegral_eq_zero_iff hmeas).mp hlaplace
  filter_upwards [hzero] with omega homega
  by_contra hlt
  have hfinite : omega ∈ {omega : ContinuousPath (OnePoint X) |
      ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega < ⊤} :=
    lt_top_iff_ne_top.mpr hlt
  rw [Set.indicator_of_mem hfinite] at homega
  exact absurd homega (by
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _)
