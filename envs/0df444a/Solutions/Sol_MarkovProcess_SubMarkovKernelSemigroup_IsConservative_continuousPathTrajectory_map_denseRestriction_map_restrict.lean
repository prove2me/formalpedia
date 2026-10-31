-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_denseRestriction_map_restrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:03:00.806439+00:00
-- url     : https://prove2.me/submissions/8510728d-c051-4376-a0a9-90afd83722fb

import Mathlib
import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_Trajectory_DenseRestrictionMarginals_931e4c17
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite marginals of dense restrictions of continuous trajectories

The finite-coordinate laws of the dense-time restriction of the canonical continuous trajectory
are the existing finite-set kernels, reindexed from physical time back to rational labels.  This
file makes no shift, Markov, strong Markov, or Hunt-process assertion.
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
# Finite marginals of dense restrictions of continuous trajectories

The finite-coordinate laws of the dense-time restriction of the canonical continuous trajectory
are the existing finite-set kernels, reindexed from physical time back to rational labels.  This
file makes no shift, Markov, strong Markov, or Hunt-process assertion.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

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
    (I : Finset DenseTime) :
    ((continuousPathTrajectory P hP default).map
        ContinuousPath.denseRestriction).map I.restrict =
      (finiteSetKernel P (denseTimePhysicalSet I)).map
        (DenseTimePath.pullbackPhysicalSet I) := by
  let evaluatePhysical : ContinuousPath alpha → denseTimePhysicalSet I → alpha :=
    fun path t ↦ path t
  have hEvaluate : Measurable evaluatePhysical := by
    rw [measurable_pi_iff]
    intro t
    rw [BorelSpace.measurable_eq (α := alpha)]
    exact (ContinuousPath.continuous_eval (alpha := alpha) (t : NNReal)).borel_measurable
  have hfun :
      I.restrict ∘ ContinuousPath.denseRestriction =
        DenseTimePath.pullbackPhysicalSet I ∘ evaluatePhysical := by
    funext path
    exact (DenseTimePath.pullbackPhysicalSet_evaluation I path).symm
  rw [← Kernel.map_comp_right]
  · rw [hfun, Kernel.map_comp_right]
    · change
        ((continuousPathTrajectory P hP default).map
          (fun path (t : denseTimePhysicalSet I) ↦ path t)).map
            (DenseTimePath.pullbackPhysicalSet I) = _
      rw [p2m_embedded_b819d8df72e216cf P hP default hK I]
    · exact hEvaluate
    · exact DenseTimePath.measurable_pullbackPhysicalSet I
  · exact ContinuousPath.measurable_denseRestriction
  · exact Finset.measurable_restrict I
