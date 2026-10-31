-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedKernel_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:25:45.725557+00:00
-- url     : https://prove2.me/submissions/7c18b31b-4b56-49da-9a03-bd537ee7a5e7

import Definitions.Def_MarkovProcess_V3H_Killed_Kernel_adff808d
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
# The process killed at the exit time of an open set: transition kernels

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
and an open set `U`, the transition kernel at time `t` of the process **killed when it leaves
`U`** is

  `killedKernel P hP U hU t x B = Q x {ω | t < exitTime U ω ∧ ω t ∈ B}`,

the law of the position at time `t` restricted to the survival event `{t < τ_U}`.  This file
proves that these kernels are sub-Markov (`isSubMarkovKernel_killedKernel`), jointly measurable
in time and starting point (`measurable_killedKernel`), vanish off `U`
(`killedKernel_apply_of_notMem`), reduce at time zero to the identity restricted to `U`
(`killedKernel_zero`), and satisfy the Chapman--Kolmogorov law `killedKernel_add`,

  `killedKernel (s + t) = killedKernel t ∘ₖ killedKernel s`,

which follows from the Markov property of `Q` at the deterministic time `s` on the
`𝓕_s`-event `{s < τ_U}` together with the path identity `{s + t < τ} = {s < τ} ∩ {t < τ ∘ θ_s}`.

On the carrier `alpha` the family is not a `SubMarkovKernelSemigroup`, because at time zero it is
the identity only on `U` (it is `0` off `U`); the semigroup structure on the carrier `U` is a
separate packaging.  No Feller property of the killed family is claimed.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]









variable [MeasurableSpace alpha] [BorelSpace alpha]





end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

















variable [LocallyCompactSpace alpha]



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
# The process killed at the exit time of an open set: transition kernels

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
and an open set `U`, the transition kernel at time `t` of the process **killed when it leaves
`U`** is

  `killedKernel P hP U hU t x B = Q x {ω | t < exitTime U ω ∧ ω t ∈ B}`,

the law of the position at time `t` restricted to the survival event `{t < τ_U}`.  This file
proves that these kernels are sub-Markov (`isSubMarkovKernel_killedKernel`), jointly measurable
in time and starting point (`measurable_killedKernel`), vanish off `U`
(`killedKernel_apply_of_notMem`), reduce at time zero to the identity restricted to `U`
(`killedKernel_zero`), and satisfy the Chapman--Kolmogorov law `killedKernel_add`,

  `killedKernel (s + t) = killedKernel t ∘ₖ killedKernel s`,

which follows from the Markov property of `Q` at the deterministic time `s` on the
`𝓕_s`-event `{s < τ_U}` together with the path identity `{s + t < τ} = {s < τ} ∩ {t < τ ∘ θ_s}`.

On the carrier `alpha` the family is not a `SubMarkovKernelSemigroup`, because at time zero it is
the identity only on `U` (it is `0` off `U`); the semigroup structure on the carrier `U` is a
separate packaging.  No Feller property of the killed family is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)















namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (hK : P.KolmogorovRegular hP) :
    IsConservative.killedKernel P hP U hU 0 = Kernel.id.restrict hU.measurableSet := by
  have hmeas0 : Measurable (fun omega : ContinuousPath alpha ↦ omega 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  refine Kernel.ext fun x ↦ Measure.ext fun B hB ↦ ?_
  have hevent : ContinuousPath.killedEvent U 0 B = (fun omega : ContinuousPath alpha ↦ omega 0) ⁻¹'
      (B ∩ U) := by
    ext omega
    simp only [ContinuousPath.mem_killedEvent_iff, ENNReal.coe_zero, Set.mem_preimage,
      Set.mem_inter_iff, ContinuousPath.exitTime_pos_iff U hU]
    exact and_comm
  rw [IsConservative.killedKernel_apply P hP U hU 0 x hB, hevent,
    ← Measure.map_apply hmeas0 (hB.inter hU.measurableSet), ← Kernel.map_apply _ hmeas0,
    IsConservative.continuousProcess_map_eval_zero P hP hK, Kernel.restrict_apply' _ _ _ hB]
