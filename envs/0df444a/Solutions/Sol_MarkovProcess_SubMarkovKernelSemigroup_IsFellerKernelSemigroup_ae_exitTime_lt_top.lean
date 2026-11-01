-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.ae_exitTime_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:40:46.374726+00:00
-- url     : https://prove2.me/submissions/ed2dad77-8bf7-4e9b-a016-e4a3cd8221f8

import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
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
import Theorems.Thm_MarkovProcess_ContinuousPath_iSup_exitTimeTrunc
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_integral_exitTimeTrunc_le
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_lintegral_exitTimeTrunc_eq

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The expected exit time, untruncated

The expected exit time bound of `Trajectory/DynkinStopping.lean` is stated for the exit time
truncated at a deterministic horizon `K`, uniformly in `K`.  This file removes the truncation by
monotone convergence: under the same hypotheses (`L f ≤ -1` on the open set `U`, `f ≥ m`),

  `E_x τ_U ≤ f x - m`  (`IsFellerKernelSemigroup.lintegral_exitTime_le`),

as an `ℝ≥0∞`-valued integral of the `ℝ≥0∞`-valued exit time, so in particular the exit time from
`U` is almost surely finite from every starting point (`ae_exitTime_lt_top`).

It also records that the truncated exit time of `Path/ExitTime.lean` is the generic truncation
`StoppingTime.truncTime` of `Trajectory/StoppingLtTop.lean` applied to `exitTimeTop`
(`ContinuousPath.exitTimeTrunc_eq_truncTime`), and the monotone limit
`ContinuousPath.iSup_exitTimeTrunc : ⨆ n, exitTimeTrunc U n ω = exitTime U ω`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]



/-- The truncated exit time, read in `ℝ≥0∞`, is the minimum of the exit time and the horizon. -/
theorem coe_exitTimeTrunc_ennreal (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) :
    ((exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) = min (exitTime U omega) (K : ℝ≥0∞) :=
  coe_exitTimeTrunc U K omega



/-- Truncations at the natural horizons are monotone in the horizon. -/
theorem monotone_exitTimeTrunc (U : Set alpha) (omega : ContinuousPath alpha) :
    Monotone fun n : ℕ ↦ ((exitTimeTrunc U n omega : NNReal) : ℝ≥0∞) := by
  intro m n hmn
  simp only [coe_exitTimeTrunc_ennreal, ENNReal.coe_natCast]
  exact min_le_min_left _ (Nat.cast_le.mpr hmn)

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha] in
/-- The truncated exit time is measurable on path space. -/
theorem measurable_coe_exitTimeTrunc (U : Set alpha) (hU : IsOpen U) (K : NNReal) :
    Measurable fun omega : ContinuousPath alpha ↦
      ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp
    (ContinuousPath.measurable_of_isStoppingTime _
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K))



/-- **The expected exit time is bounded, without truncation.**  If `L f ≤ -1` on the open set `U`
and `f ≥ m`, then the exit time from `U` has expectation at most `f x - m` from every starting
point, as an `ℝ≥0∞`-valued integral. -/
theorem IsFellerKernelSemigroup.lintegral_exitTime_le (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y ≤ -1) {m : ℝ}
    (hm : ∀ y, m ≤ (f : C₀(alpha, ℝ)) y) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP x) ≤
      ENNReal.ofReal ((f : C₀(alpha, ℝ)) x - m) := by
  have hsup : (fun omega : ContinuousPath alpha ↦ ContinuousPath.exitTime U omega) =
      fun omega ↦ ⨆ n : ℕ, ((ContinuousPath.exitTimeTrunc U n omega : NNReal) : ℝ≥0∞) :=
    funext fun omega ↦ (ContinuousPath.iSup_exitTimeTrunc U omega).symm
  rw [hsup, lintegral_iSup (fun n ↦ measurable_coe_exitTimeTrunc U hU n)
    (fun m n hmn omega ↦ ContinuousPath.monotone_exitTimeTrunc U omega hmn)]
  refine iSup_le fun n ↦ ?_
  rw [lintegral_exitTimeTrunc_eq hP U hU n x]
  exact ENNReal.ofReal_le_ofReal (hFeller.integral_exitTimeTrunc_le hP hK f U hU hLf hm n x)



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
# The expected exit time, untruncated

The expected exit time bound of `Trajectory/DynkinStopping.lean` is stated for the exit time
truncated at a deterministic horizon `K`, uniformly in `K`.  This file removes the truncation by
monotone convergence: under the same hypotheses (`L f ≤ -1` on the open set `U`, `f ≥ m`),

  `E_x τ_U ≤ f x - m`  (`IsFellerKernelSemigroup.lintegral_exitTime_le`),

as an `ℝ≥0∞`-valued integral of the `ℝ≥0∞`-valued exit time, so in particular the exit time from
`U` is almost surely finite from every starting point (`ae_exitTime_lt_top`).

It also records that the truncated exit time of `Path/ExitTime.lean` is the generic truncation
`StoppingTime.truncTime` of `Trajectory/StoppingLtTop.lean` applied to `exitTimeTop`
(`ContinuousPath.exitTimeTrunc_eq_truncTime`), and the monotone limit
`ContinuousPath.iSup_exitTimeTrunc : ⨆ n, exitTimeTrunc U n ω = exitTime U ω`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}







namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y ≤ -1) {m : ℝ}
    (hm : ∀ y, m ≤ (f : C₀(alpha, ℝ)) y) (x : alpha) :
    ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x), ContinuousPath.exitTime U omega < ⊤ :=
  ae_lt_top (ContinuousPath.measurable_exitTime U hU)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hFeller.lintegral_exitTime_le hP hK f U hU hLf hm x))
