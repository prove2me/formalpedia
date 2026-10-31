-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_map_finiteEvaluation_denseTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:10:22.828535+00:00
-- url     : https://prove2.me/submissions/d563f9af-9ee3-4c12-89cd-99a48d9845c9

import Mathlib
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













/-- Every finite rational-time marginal of the continuous-path process is the finite-set kernel of
`P` at the corresponding physical times. -/
theorem IsConservative.continuousProcess_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (I : Finset DenseTime) :
    (continuousProcess P hP).map
        (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
      finiteSetKernel P (denseTimePhysicalSet I) :=
  p2m_embedded_b819d8df72e216cf P hP _ hK I





variable [LocallyCompactSpace alpha]









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

/-- Evaluation of a continuous path at a finite set of times is measurable. -/
theorem measurable_finsetEvaluation (I : Finset NNReal) :
    Measurable (finsetEvaluation (alpha := alpha) I) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_coordinateProcess (alpha := alpha) (t : NNReal)

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









namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative
theorem solution
    (hK : P.KolmogorovRegular hP) (theta : Theta) (x : alpha) (I : Finset DenseTime) :
    (IsConservative.continuousProcess P hP (theta, x)).map
        (ContinuousPath.finsetEvaluation (SubMarkovKernelSemigroup.denseTimePhysicalSet I)) =
      SubMarkovKernelSemigroup.finiteSetKernel (P.toSubMarkovKernelSemigroup theta)
        (SubMarkovKernelSemigroup.denseTimePhysicalSet I) x := by
  rw [IsConservative.continuousProcess_apply,
    ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
    SubMarkovKernelSemigroup.IsConservative.continuousProcess_map_finiteEvaluation_denseTime _ _
      (hK theta)]
