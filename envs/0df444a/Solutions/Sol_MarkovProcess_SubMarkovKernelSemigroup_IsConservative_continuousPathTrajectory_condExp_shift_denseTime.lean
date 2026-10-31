-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_condExp_shift_denseTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:50:59.875741+00:00
-- url     : https://prove2.me/submissions/0105bdf0-21df-4c8f-b4cc-fcc4ce48df7b

import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestart_9d6a4f09
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestrictedRestart_3bd46ae7
import Definitions.Def_MarkovProcess_V3H_Trajectory_RationalConditional_eedb6623
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
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
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite
import Theorems.Thm_MarkovProcess_ContinuousPath_condExp_shift_ae_eq_integral_pathKernel_of_restrict_map

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Rational-time conditional Markov identities for the continuous trajectory

This file derives two local consequences of the rational joint restart law for the canonical
continuous-path trajectory.  First, restricting to any event in the canonical filtration and
then shifting at a rational time gives the path kernel restarted from the state at that time.
Second, every bounded strongly measurable functional of the shifted path satisfies the
corresponding conditional-expectation formula.

The times here are rational.  The strong Markov property at an arbitrary finite stopping time
is in `Trajectory/FellerStoppingRestart.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]





variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]



end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Rational-time conditional Markov identities for the continuous trajectory

This file derives two local consequences of the rational joint restart law for the canonical
continuous-path trajectory.  First, restricting to any event in the canonical filtration and
then shifting at a rational time gives the path kernel restarted from the state at that time.
Second, every bounded strongly measurable functional of the shifted path satisfies the
corresponding conditional-expectation formula.

The times here are rational.  The strong Markov property at an arbitrary finite stopping time
is in `Trajectory/FellerStoppingRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]





variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (S : DenseTime)
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)|
      ContinuousPath.canonicalFiltration (alpha := alpha)
        (DenseTime.castOrderEmbedding S)] =ᵐ[(continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega (DenseTime.castOrderEmbedding S)) := by
  apply ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    (continuousPathTrajectory P hP default) x (DenseTime.castOrderEmbedding S)
  · exact continuousPathTrajectory_restrict_map_shift_denseTime P hP default hK x S
  · exact hF
  · exact hFC
