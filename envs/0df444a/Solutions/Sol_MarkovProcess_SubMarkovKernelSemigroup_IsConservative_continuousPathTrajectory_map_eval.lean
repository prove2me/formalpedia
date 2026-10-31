-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_eval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:14:58.416253+00:00
-- url     : https://prove2.me/submissions/016e6045-59d9-4fdf-8d36-125579ed4419

import Definitions.Def_MarkovProcess_V3H_Continuity_KolmogorovDenseTimeContinuousSupport_e9ca7f43
import Definitions.Def_MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_denseTimeTrajectory_map_eval

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous-path trajectory kernels

This file transports the canonical dense-time trajectory of a conservative kernel semigroup to
continuous paths.  The explicit default is used only by the previously established measurable
extension away from the continuous-restriction range.  A coordinate Kolmogorov condition makes
that fallback irrelevant and transports the proved rational-time marginal identities.

No continuous-time Markov property, strong Markov property, Hunt-process assertion, or PDE
increment estimate is claimed.
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
# Continuous-path trajectory kernels

This file transports the canonical dense-time trajectory of a conservative kernel semigroup to
continuous paths.  The explicit default is used only by the previously established measurable
extension away from the continuous-restriction range.  A coordinate Kolmogorov condition makes
that fallback irrelevant and transports the proved rational-time marginal identities.

No continuous-time Markov property, strong Markov property, Hunt-process assertion, or PDE
increment estimate is claimed.
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
    (r : DenseTime) :
    (continuousPathTrajectory P hP default).map
        (fun path ↦ path (DenseTime.castOrderEmbedding r)) =
      P (DenseTime.castOrderEmbedding r) := by
  let kappa := denseTimeTrajectory P hP DenseTime.enumeration
    DenseTime.castOrderEmbedding.toEmbedding
  have hback :
      (continuousPathTrajectory P hP default).map ContinuousPath.denseRestriction = kappa := by
    exact Kernel.map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
      kappa default hK
  have hfun :
      (fun path : ContinuousPath alpha ↦ path (DenseTime.castOrderEmbedding r)) =
        (fun path : DenseTime → alpha ↦ path r) ∘ ContinuousPath.denseRestriction := by
    rfl
  rw [hfun, Kernel.map_comp_right]
  · rw [hback]
    exact denseTimeTrajectory_map_eval P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding r
  · exact ContinuousPath.measurable_denseRestriction
  · exact measurable_pi_apply r
