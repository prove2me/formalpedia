-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess_map_killedCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:59:56.403059+00:00
-- url     : https://prove2.me/submissions/e59b993f-69dd-4fd6-9b5c-e11d0e5e30da

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeterySemigroup_149c26e5
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_Killed_Nested_fac741d0
import Definitions.Def_MarkovProcess_V3H_Killed_Process_a15f3c27
import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTimeStopping_1c91d085
import Definitions.Def_MarkovProcess_V3H_Path_Exhaustion_e03721f1
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
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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
import Theorems.Thm_MarkovProcess_ContinuousPath_lifetimePath_exitTime_killAtExit
import Theorems.Thm_MarkovProcess_LifetimePath_measurable_killedCoordinate

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The process killed at the exit of an open set, as a law on lifetime paths

For the continuous-path process `Q = continuousProcess P hP` of a conservative semigroup and an
open set `U`, killing each path at its exit time from `U` produces a Markov kernel

  `killedProcess P hP U hU : Kernel U (LifetimePath U)`,

the law of the process started inside `U` and sent to the cemetery when it leaves `U`.  It is the
image of `Q` under `ContinuousPath.killAtExit U`, pulled back to the carrier `U`.

Two marginals are identified here.  The lifetime of the killed process is the exit time
(`killedProcess_map_lifetime`), and its coordinate at a fixed time is the cemetery extension of
the killed transition kernel on `U` (`killedProcess_map_coordinate`): the live part is
`killedKernelOn P hP U hU t x` and the cemetery carries exactly the mass lost by time `t`.

No finite-dimensional distribution of the killed process is identified here, and no Feller or
regularity property of the killed family is claimed.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace LifetimePath



end LifetimePath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)







/-- The killed process started at `x ∈ U` is the law of the process started at `x`, pushed forward
by killing at the exit time of `U`. -/
theorem IsConservative.killedProcess_apply (x : U) :
    IsConservative.killedProcess P hP U hU x =
      (IsConservative.continuousProcess P hP (x : alpha)).map (ContinuousPath.killAtExit U) := by
  rw [IsConservative.killedProcess_eq_map,
    Kernel.map_apply _ (ContinuousPath.measurable_killAtExit U hU), Kernel.comap_apply]









end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times along an exhaustion

For an increasing sequence of open sets `U n` covering the state space (an open exhaustion), the
exit time of a continuous path from `U n` tends to infinity: the path restricted to a compact time
interval has compact range, which lies in some `U N`, and the path therefore stays in `U n` on that
interval for every `n ≥ N` (`tendsto_exitTime_atTop`).  Exit times are monotone in the set
(`exitTime_mono`), as are the truncated exit times.

This is the path-space fact behind nonexplosion arguments: no probability law is involved here.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace MarkovProcess.ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- Exit times are monotone in the set: a path leaves a larger set no earlier. -/
theorem exitTime_mono {U V : Set alpha} (hUV : U ⊆ V) (omega : ContinuousPath alpha) :
    exitTime U omega ≤ exitTime V omega := by
  rw [le_exitTime_iff]
  intro v hv
  exact exitTime_le_of_notMem U omega v (fun h ↦ hv (hUV h))















end MarkovProcess.ContinuousPath


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Nested domains: killing at the exit of a smaller set

For two sets `U ⊆ V` the path killed at the exit of `U` is the path killed at the exit of `V`,
killed once more at the exit of `U`.  This file proves that relation on path space and transports
it to the killed processes.

* `ContinuousPath.exitTime_mono`: a path leaves a smaller set no later;
* `LifetimePath.killedCoordinate W t`: the coordinate at time `t` of a lifetime path killed once
  more at the exit of `W`, together with its two coordinate formulas and its measurability for an
  open `W` (`LifetimePath.measurable_killedCoordinate`), which rests on the measurability of the
  lifetime-path exit time `LifetimePath.measurable_exitTime` proved here;
* `ContinuousPath.lifetimePath_exitTime_killAtExit`: the first time the `V`-killed path is not a
  live point of `U` is the exit time of `U`, that is, the lifetime of the `U`-killed path;
* `ContinuousPath.killedCoordinate_killAtExit`: killing the `V`-killed path once more at the exit
  of `U` reads, at every time, the coordinate of the `U`-killed path through the inclusion of `U`
  in `V`;
* `killedProcess_map_exitTime` and `killedProcess_map_killedCoordinates`: the same two statements
  for the laws, and finally `killedProcess_map_killedFinsetCoordinates`, the part-process property
  at the level of the finite-dimensional distributions: the process of `V` killed again at the
  exit of `U` has the finite-dimensional distributions of the cemetery extension of the killed
  semigroup on `U`.

The carriers of the two killed processes are the subtypes `U` and `V`, which are different types;
the statements here compare them through the inclusion of `U` in `V` rather than identifying the
two killed processes as laws on a common carrier.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace LifetimePath

section Killing

variable {beta : Type*} [PseudoMetricSpace beta]







end Killing

section MeasurableExitTime

variable {beta : Type*} [PseudoMetricSpace beta] [MeasurableSpace beta] [BorelSpace beta]





end MeasurableExitTime

end LifetimePath

namespace ContinuousPath

section Nested

variable {alpha : Type*} [PseudoMetricSpace alpha] {U V : Set alpha}



/-- Strictly before the exit time of `U`, the `V`-killed path is alive at the point where the
`U`-killed path is alive, matched by the inclusion of `U` in `V`. -/
theorem coordinate_killAtExit_inclusion (hUV : U ⊆ V) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : (t : ℝ≥0∞) < exitTime U omega) :
    LifetimePath.coordinate t (killAtExit V omega) =
      Cemetery.alive (Set.inclusion hUV ⟨omega t, mem_of_lt_exitTime U omega t ht⟩) :=
  coordinate_killAtExit_of_lt V omega t (ht.trans_le (exitTime_mono hUV omega))

/-- Killing the `V`-killed path once more at the exit of `U` reads, at every time, the coordinate
of the `U`-killed path through the inclusion of `U` in `V`. -/
theorem killedCoordinate_killAtExit (hUV : U ⊆ V) (omega : ContinuousPath alpha) (t : NNReal) :
    LifetimePath.killedCoordinate (Subtype.val ⁻¹' U : Set V) t (killAtExit V omega) =
      Sum.map (Set.inclusion hUV) id (LifetimePath.coordinate t (killAtExit U omega)) := by
  rw [LifetimePath.killedCoordinate, lifetimePath_exitTime_killAtExit hUV omega]
  by_cases hlt : (t : ℝ≥0∞) < exitTime U omega
  · rw [if_pos hlt, coordinate_killAtExit_inclusion hUV omega t hlt,
      coordinate_killAtExit_of_lt U omega t hlt]
    rfl
  · rw [if_neg hlt, coordinate_killAtExit_of_le U omega t (not_lt.mp hlt)]
    rfl

end Nested

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U V : Set alpha)





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
# Nested domains: killing at the exit of a smaller set

For two sets `U ⊆ V` the path killed at the exit of `U` is the path killed at the exit of `V`,
killed once more at the exit of `U`.  This file proves that relation on path space and transports
it to the killed processes.

* `ContinuousPath.exitTime_mono`: a path leaves a smaller set no later;
* `LifetimePath.killedCoordinate W t`: the coordinate at time `t` of a lifetime path killed once
  more at the exit of `W`, together with its two coordinate formulas and its measurability for an
  open `W` (`LifetimePath.measurable_killedCoordinate`), which rests on the measurability of the
  lifetime-path exit time `LifetimePath.measurable_exitTime` proved here;
* `ContinuousPath.lifetimePath_exitTime_killAtExit`: the first time the `V`-killed path is not a
  live point of `U` is the exit time of `U`, that is, the lifetime of the `U`-killed path;
* `ContinuousPath.killedCoordinate_killAtExit`: killing the `V`-killed path once more at the exit
  of `U` reads, at every time, the coordinate of the `U`-killed path through the inclusion of `U`
  in `V`;
* `killedProcess_map_exitTime` and `killedProcess_map_killedCoordinates`: the same two statements
  for the laws, and finally `killedProcess_map_killedFinsetCoordinates`, the part-process property
  at the level of the finite-dimensional distributions: the process of `V` killed again at the
  exit of `U` has the finite-dimensional distributions of the cemetery extension of the killed
  semigroup on `U`.

The carriers of the two killed processes are the subtypes `U` and `V`, which are different types;
the statements here compare them through the inclusion of `U` in `V` rather than identifying the
two killed processes as laws on a common carrier.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal





variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U V : Set alpha)



namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (hUV : U ⊆ V) (hU : IsOpen U)
    (hV : IsOpen V) (x : U) {iota : Type*} (tau : iota → NNReal) :
    (IsConservative.killedProcess P hP V hV (Set.inclusion hUV x)).map
        (fun eta ↦ fun i ↦
          LifetimePath.killedCoordinate (Subtype.val ⁻¹' U : Set V) (tau i) eta) =
      (IsConservative.killedProcess P hP U hU x).map
        (fun omega ↦ fun i ↦
          Sum.map (Set.inclusion hUV) id (LifetimePath.coordinate (tau i) omega)) := by
  have hW : IsOpen (Subtype.val ⁻¹' U : Set V) := hU.preimage continuous_subtype_val
  have hm1 : Measurable fun eta : LifetimePath V ↦ fun i ↦
      LifetimePath.killedCoordinate (Subtype.val ⁻¹' U : Set V) (tau i) eta :=
    measurable_pi_lambda _ fun i ↦
      LifetimePath.measurable_killedCoordinate _ hW (tau i)
  have hm2 : Measurable fun omega : LifetimePath U ↦ fun i ↦
      Sum.map (Set.inclusion hUV) id (LifetimePath.coordinate (tau i) omega) :=
    measurable_pi_lambda _ fun i ↦
      ((measurable_inclusion hUV).sumMap measurable_id).comp
        (LifetimePath.measurable_coordinate (tau i))
  have hfun : (fun eta : LifetimePath V ↦ fun i ↦
        LifetimePath.killedCoordinate (Subtype.val ⁻¹' U : Set V) (tau i) eta) ∘
      ContinuousPath.killAtExit V =
      (fun omega : LifetimePath U ↦ fun i ↦
        Sum.map (Set.inclusion hUV) id (LifetimePath.coordinate (tau i) omega)) ∘
      ContinuousPath.killAtExit U := by
    funext omega i
    exact ContinuousPath.killedCoordinate_killAtExit hUV omega (tau i)
  rw [IsConservative.killedProcess_apply P hP V hV (Set.inclusion hUV x),
    IsConservative.killedProcess_apply P hP U hU x,
    Measure.map_map hm1 (ContinuousPath.measurable_killAtExit V hV),
    Measure.map_map hm2 (ContinuousPath.measurable_killAtExit U hU), hfun]
