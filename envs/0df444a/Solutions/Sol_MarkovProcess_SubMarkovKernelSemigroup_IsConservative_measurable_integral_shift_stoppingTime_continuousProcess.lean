-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.measurable_integral_shift_stoppingTime_continuousProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:27:34.480165+00:00
-- url     : https://prove2.me/submissions/8abaddf3-6697-4392-8f84-e5a26859ec71

import Definitions.Def_MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Tight
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
# Measurability of random shifts of continuous paths

Shifting a continuous path by a Borel measurable random time, and evaluating it at that time,
are Borel measurable, because the deterministic shift and the evaluation are jointly continuous
in the time and the path.  A finite `NNReal`-valued stopping time for the canonical filtration is
such a random time.  No countable-range premise is used.

This is ordinary measurability infrastructure.  It proves no restart identity and no conditional
expectation formula; those are in `Trajectory/FellerStoppingRestart.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Shifting by a Borel measurable random time is Borel measurable. -/
theorem measurable_shift_of_measurable (T : ContinuousPath alpha → NNReal)
    (hT : Measurable T) :
    Measurable (fun omega ↦ shift (T omega) omega) := by
  have hpair : Measurable (fun omega : ContinuousPath alpha ↦ (T omega, omega)) :=
    hT.prodMk measurable_id
  exact (continuous_shift (alpha := alpha)).measurable.comp hpair

variable [MeasurableSpace alpha] [BorelSpace alpha]





/-- Shifting by a finite stopping time for the canonical filtration is Borel measurable. -/
theorem measurable_shift_stoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable (fun omega ↦ shift (T omega) omega) :=
  measurable_shift_of_measurable T (measurable_of_isStoppingTime T hT)



end ContinuousPath
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurable and continuous dependence on the starting point

Two regularity statements for the continuous-path process of a conservative sub-Markov kernel
semigroup, both in the starting point.

*Measurability.*  For a strongly measurable functional `F` of the path, the expectation
`x ↦ ∫ F d(continuousProcess P hP x)` is strongly measurable, hence measurable into a Borel
target: `IsConservative.stronglyMeasurable_integral_continuousProcess` and
`IsConservative.measurable_integral_continuousProcess`.  The same holds for the two functionals
that the strong Markov property produces, the shifted path and the state at a finite stopping
time: `IsConservative.measurable_integral_shift_stoppingTime_continuousProcess` and
`IsConservative.measurable_integral_eval_stoppingTime_continuousProcess`.

*Continuity.*  For a Feller semigroup the finite-dimensional laws depend weakly continuously on
the starting point: `IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel`
upgrades compact-test continuity to all bounded continuous test functions.  The
upgrade is a tightness argument: a finite-dimensional law on a Polish coordinate space is tight,
so a compactly supported continuous cutoff `g` with `1_K ≤ g ≤ 1` captures all but `epsilon` of the
mass at the reference starting point, the truncated integral `∫ f * g` is continuous by the
compact-test theorem, and the discarded part is bounded by `‖f‖ * (1 - ∫ g)`, itself continuous
and small.  On the process this reads as continuity of cylinder expectations,
`IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess`, with the
one-time case `IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess`.

Nothing here asserts weak continuity of the full path law `x ↦ continuousProcess P hP x` on path
space; that needs tightness on path space itself, which is not proved here.  No statement covers
a stopping time that can be infinite.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction CompactlySupported NNReal

namespace MarkovProcess


namespace SubMarkovKernelSemigroup

section BoundedContinuousTest

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [LocallyCompactSpace alpha]



end BoundedContinuousTest

noncomputable section Process

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

section Measurability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Expectations of the process are strongly measurable in the starting point.**  For a
strongly measurable functional `F` on continuous paths, `x ↦ ∫ F d(continuousProcess P hP x)` is
strongly measurable; this is the kernel integral of a strongly measurable function, so no
regularity hypothesis on `P` beyond conservativity is needed. -/
theorem IsConservative.stronglyMeasurable_integral_continuousProcess
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F) :
    StronglyMeasurable fun x ↦ ∫ eta, F eta ∂(continuousProcess P hP x) :=
  hF.integral_kernel (κ := continuousProcess P hP)

variable [MeasurableSpace E] [BorelSpace E]

/-- **Expectations of the process are measurable in the starting point.**  Borel-target form of
`stronglyMeasurable_integral_continuousProcess`: the map `x ↦ ∫ F d(continuousProcess P hP x)` is
measurable for every strongly measurable functional `F` on continuous paths. -/
theorem IsConservative.measurable_integral_continuousProcess
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F) :
    Measurable fun x ↦ ∫ eta, F eta ∂(continuousProcess P hP x) :=
  (IsConservative.stronglyMeasurable_integral_continuousProcess P hP F hF).measurable





end Measurability

section Continuity

variable [LocallyCompactSpace alpha]





end Continuity

end Process

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
# Measurable and continuous dependence on the starting point

Two regularity statements for the continuous-path process of a conservative sub-Markov kernel
semigroup, both in the starting point.

*Measurability.*  For a strongly measurable functional `F` of the path, the expectation
`x ↦ ∫ F d(continuousProcess P hP x)` is strongly measurable, hence measurable into a Borel
target: `IsConservative.stronglyMeasurable_integral_continuousProcess` and
`IsConservative.measurable_integral_continuousProcess`.  The same holds for the two functionals
that the strong Markov property produces, the shifted path and the state at a finite stopping
time: `IsConservative.measurable_integral_shift_stoppingTime_continuousProcess` and
`IsConservative.measurable_integral_eval_stoppingTime_continuousProcess`.

*Continuity.*  For a Feller semigroup the finite-dimensional laws depend weakly continuously on
the starting point: `IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel`
upgrades compact-test continuity to all bounded continuous test functions.  The
upgrade is a tightness argument: a finite-dimensional law on a Polish coordinate space is tight,
so a compactly supported continuous cutoff `g` with `1_K ≤ g ≤ 1` captures all but `epsilon` of the
mass at the reference starting point, the truncated integral `∫ f * g` is continuous by the
compact-test theorem, and the discarded part is bounded by `‖f‖ * (1 - ∫ g)`, itself continuous
and small.  On the process this reads as continuity of cylinder expectations,
`IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess`, with the
one-time case `IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess`.

Nothing here asserts weak continuity of the full path law `x ↦ continuousProcess P hP x` on path
space; that needs tightness on path space itself, which is not proved here.  No statement covers
a stopping time that can be infinite.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction CompactlySupported NNReal






open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



variable [MeasurableSpace E] [BorelSpace E]



namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F) :
    Measurable fun x ↦ ∫ omega, F (ContinuousPath.shift (T omega) omega)
      ∂(continuousProcess P hP x) :=
  IsConservative.measurable_integral_continuousProcess P hP _
    (hF.comp_measurable (ContinuousPath.measurable_shift_stoppingTime T hT))
