-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_restrict_map_shift_stoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:14:14.60982+00:00
-- url     : https://prove2.me/submissions/beab8f6e-0511-4f2a-bd84-77ba93784dd8

import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
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
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuousPathTrajectory_restrict_map_shift_stoppingTime

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The continuous-path Markov process of a Feller semigroup

This is the entry point of the library: for a conservative sub-Markov kernel semigroup `P` on a
nonempty, locally compact Polish state space it names the continuous-path process
`continuousProcess P hP`, restates under quotable names the properties proved for that process
elsewhere in the library, and proves that it is the unique Markov kernel into continuous paths
with the finite-dimensional distributions of `P`.

Every statement carries the Kolmogorov regularity hypothesis `P.KolmogorovRegular hP`, which is
what gives the dense-time trajectory of `P` a continuous modification.  The shift and restart
statements carry in addition the Feller hypothesis `P.IsFellerKernelSemigroup`; the uniqueness
statements carry neither Feller continuity nor local compactness.

Nothing here asserts a Hunt-process property, and no statement covers a stopping time that can be
infinite.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

section FinsetEvaluation

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



end ContinuousPath

end FinsetEvaluation

namespace Kernel

noncomputable section DenseFiniteEvaluation

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]



section Identification

variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]



end Identification

end DenseFiniteEvaluation

end Kernel

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



















variable [LocallyCompactSpace alpha]







/-- Strong Markov property at a finite stopping time, in restart form: after restriction to an
event of the stopped sigma-algebra, the law of the path shifted at the stopping time is the
process started from the state at that time. -/
theorem IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (A : Set (ContinuousPath alpha)) (hA : MeasurableSet[hT.measurableSpace] A) :
    (((continuousProcess P hP) x).restrict A).map
        (fun omega ↦ ContinuousPath.shift (T omega) omega) =
      Kernel.comap (continuousProcess P hP) (fun omega ↦ omega (T omega))
          (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
        (((continuousProcess P hP) x).restrict A) :=
  hFeller.continuousPathTrajectory_restrict_map_shift_stoppingTime P hP _ hK x T hT A hA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]




















end


end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Properties of the parameterized continuous-path process

Every property of the continuous-path process of a single semigroup, as exposed in
`MarkovProcess/Main.lean`, restated for the measurably parameterized process
`ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP` at a point
`(theta, x)` of the parameter-and-state space.  The hypotheses are the fibrewise ones: fibrewise
conservativity `hP`, fibrewise Feller property `hFeller` where the single-semigroup statement needs
it, and fibrewise Kolmogorov regularity `hK`.

Every proof is a transport through the exact fibre identity
`IsConservative.continuousProcess_apply`; consumers never need that identity themselves.  The
restarted kernels are written as the parameterized kernel composed with the map
`omega ↦ (theta, omega (T omega))`, so that the parameter is carried along the restart.

Main statements: `continuousProcess_map_eval`, `continuousProcess_map_eval_zero` (and its kernel
form `continuousProcess_map_eval_zero'`), `continuousProcess_map_finiteEvaluation`,
`continuousProcess_map_finiteEvaluation_denseTime`, `continuousProcess_map_shift`,
`continuousProcess_restrict_map_shift`, `continuousProcess_restrict_map_shift_stoppingTime`,
`continuousProcess_condExp_shift`, `continuousProcess_condExp_shift_stoppingTime`,
`continuousProcess_condExp_shift_countableStoppingTime`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]



end ContinuousPath

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)

section Fibre







end Fibre

section Marginals









variable [LocallyCompactSpace alpha]
  (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)

include hFeller









variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]







end Marginals

end ParameterizedSubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Properties of the parameterized continuous-path process

Every property of the continuous-path process of a single semigroup, as exposed in
`MarkovProcess/Main.lean`, restated for the measurably parameterized process
`ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP` at a point
`(theta, x)` of the parameter-and-state space.  The hypotheses are the fibrewise ones: fibrewise
conservativity `hP`, fibrewise Feller property `hFeller` where the single-semigroup statement needs
it, and fibrewise Kolmogorov regularity `hK`.

Every proof is a transport through the exact fibre identity
`IsConservative.continuousProcess_apply`; consumers never need that identity themselves.  The
restarted kernels are written as the parameterized kernel composed with the map
`omega ↦ (theta, omega (T omega))`, so that the parameter is carried along the restart.

Main statements: `continuousProcess_map_eval`, `continuousProcess_map_eval_zero` (and its kernel
form `continuousProcess_map_eval_zero'`), `continuousProcess_map_finiteEvaluation`,
`continuousProcess_map_finiteEvaluation_denseTime`, `continuousProcess_map_shift`,
`continuousProcess_restrict_map_shift`, `continuousProcess_restrict_map_shift_stoppingTime`,
`continuousProcess_condExp_shift`, `continuousProcess_condExp_shift_stoppingTime`,
`continuousProcess_condExp_shift_countableStoppingTime`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal




variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)











variable [LocallyCompactSpace alpha]
  (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)

include hFeller







namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative
theorem solution
    (hK : P.KolmogorovRegular hP) (theta : Theta) (x : alpha)
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (A : Set (ContinuousPath alpha)) (hA : MeasurableSet[hT.measurableSpace] A) :
    ((IsConservative.continuousProcess P hP (theta, x)).restrict A).map
        (fun omega ↦ ContinuousPath.shift (T omega) omega) =
      Kernel.comap (IsConservative.continuousProcess P hP)
          (fun omega ↦ (theta, omega (T omega)))
          (measurable_prodMk_eval_stoppingTime theta T hT)
        ∘ₘ ((IsConservative.continuousProcess P hP (theta, x)).restrict A) := by
  have h := (hFeller theta).continuousProcess_restrict_map_shift_stoppingTime _ _ (hK theta) x T
    hT A hA
  rw [IsConservative.continuousProcess_apply]
  refine h.trans (congrArg (Measure.bind _) ?_)
  funext omega
  exact (IsConservative.continuousProcess_apply P hP theta (omega (T omega))).symm
