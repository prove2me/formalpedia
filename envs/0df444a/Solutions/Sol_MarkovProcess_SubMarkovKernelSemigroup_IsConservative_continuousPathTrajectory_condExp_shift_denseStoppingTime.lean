-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_condExp_shift_denseStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:56:37.048005+00:00
-- url     : https://prove2.me/submissions/e6f2bc5c-9a9e-4905-beb8-69b4f91f9355

import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
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
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
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
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite
import Theorems.Thm_MarkovProcess_ContinuousPath_condExp_shift_stoppingTime_ae_eq_integral_pathKernel_of_restart_on_range

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional restart at dense-time-valued stopping times

This file specializes the countable-range stopping-time restart theorem to stopping times valued
in `DenseTime`.  The associated physical stopping time is obtained through
`DenseTime.castOrderEmbedding`; its range is countable, and deterministic restart is required and
proved only at physical times attained by that range.

The result is a conditional-expectation identity for the canonical continuous trajectory at
dense-time-valued stopping times.  An arbitrary finite `NNReal`-valued stopping time is covered
in `Trajectory/FellerStoppingConditional.lean`, and a stopping time that may be infinite in
`Trajectory/StoppingLtTop.lean`.
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

variable {alpha E : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]



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
# Conditional restart at dense-time-valued stopping times

This file specializes the countable-range stopping-time restart theorem to stopping times valued
in `DenseTime`.  The associated physical stopping time is obtained through
`DenseTime.castOrderEmbedding`; its range is countable, and deterministic restart is required and
proved only at physical times attained by that range.

The result is a conditional-expectation identity for the canonical continuous trajectory at
dense-time-valued stopping times.  An arbitrary finite `NNReal`-valued stopping time is covered
in `Trajectory/FellerStoppingConditional.lean`, and a stopping time that may be infinite in
`Trajectory/StoppingLtTop.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal



variable {alpha E : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

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
    (x : alpha) (tau : ContinuousPath alpha → DenseTime)
    (htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦
        ((DenseTime.castOrderEmbedding (tau omega) : NNReal) : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift (DenseTime.castOrderEmbedding (tau omega)) omega)|
      htau.measurableSpace] =ᵐ[(continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega (DenseTime.castOrderEmbedding (tau omega))) := by
  let tauPhysical : ContinuousPath alpha → NNReal :=
    fun omega ↦ DenseTime.castOrderEmbedding (tau omega)
  have htauRange : (Set.range tauPhysical).Countable := by
    apply (Set.countable_range
      (fun t : DenseTime ↦ DenseTime.castOrderEmbedding t)).mono
    rintro S ⟨omega, rfl⟩
    exact ⟨tau omega, rfl⟩
  apply ContinuousPath.condExp_shift_stoppingTime_ae_eq_integral_pathKernel_of_restart_on_range
    (continuousPathTrajectory P hP default) x tauPhysical htau htauRange
  · intro S hS
    obtain ⟨omega, homega⟩ := hS
    subst S
    exact continuousPathTrajectory_restrict_map_shift_denseTime
      P hP default hK x (tau omega)
  · exact hF
  · exact hFC
