-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:49:39.092069+00:00
-- url     : https://prove2.me/submissions/fc2bd054-3fed-4198-a1b5-c098d0ca49ff

import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Definitions.Def_MarkovProcess_Trajectory_Basic
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
import Theorems.Thm_MarkovProcess_Kernel_IsSupportedOnContinuousPaths_map_denseRestriction
import Theorems.Thm_MarkovProcess_Kernel_IsSupportedOnContinuousPaths_of_isKolmogorovCoordinate
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_enumeratedDenseTimeTrajectory_map_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kolmogorov support for dense-time trajectory kernels

This file applies the global dyadic-floor modification to the coordinate process of a
dense-time trajectory kernel.  A parameterwise Kolmogorov moment condition implies that the
dense-time law is supported on restrictions of continuous paths.

No measurability of the totalized modification as a path-valued map, PDE increment estimate,
Markov property of the resulting paths, or Hunt-process assertion is made here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha]



section ContinuousPathKernel

/-- Under the coordinate Kolmogorov estimate, transporting to continuous paths and restricting
back to dense time recovers the original trajectory kernel.  The path-space transport uses only
the already established measurable extension map. -/
theorem map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
    (kappa : Kernel beta (DenseTime → alpha)) [IsMarkovKernel kappa]
    (default : ContinuousPath alpha)
    (hK : ∀ b, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r) (kappa b) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p) :
    (toContinuousPathKernel kappa default).map ContinuousPath.denseRestriction = kappa := by
  exact IsSupportedOnContinuousPaths.map_denseRestriction kappa
    (IsSupportedOnContinuousPaths.of_isKolmogorovCoordinate kappa hK) default
end ContinuousPathKernel
end Kernel
end
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Trajectories on countable dense time

This file transports the finite-history transition kernels to the history carrier used by
Mathlib's Ionescu--Tulcea construction, starts the resulting trajectory at a deterministic state,
and reindexes its positive coordinates by a countable dense-time enumeration.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]















































omit [StandardBorelSpace α] [Nonempty α] in
/-- Restriction to the first `n` dense-time labels is measurable. -/
theorem measurable_denseTimeTrajectoryPrefix (e : ℕ ≃ D) (n : ℕ) :
    Measurable (denseTimeTrajectoryPrefix (α := α) e n) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (X := fun _ : D ↦ α) (e i)

omit [StandardBorelSpace α] [Nonempty α] in
private theorem denseTimeTrajectoryPrefix_measurableEquivPath
    (e : ℕ ≃ D) (n : ℕ) :
    denseTimeTrajectoryPrefix (α := α) e n ∘
        CountableEnumeration.measurableEquivPath e α =
      enumeratedDenseTimePrefix n := by
  funext path i
  dsimp only [Function.comp_apply, denseTimeTrajectoryPrefix,
    enumeratedDenseTimePrefix]
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : D ↦ α) e path i

/-- Restricting the dense-time-labelled trajectory to the first `n` enumerated labels gives
exactly the prescribed enumeration-prefix law. -/
theorem denseTimeTrajectory_map_prefix
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (denseTimeTrajectory P hP e ι).map
        (denseTimeTrajectoryPrefix e n) =
      denseTimePrefixKernel P e ι n := by
  rw [denseTimeTrajectory, ← Kernel.map_comp_right]
  · rw [denseTimeTrajectoryPrefix_measurableEquivPath]
    exact enumeratedDenseTimeTrajectory_map_prefix P hP e ι n
  · exact (CountableEnumeration.measurableEquivPath e α).measurable
  · exact measurable_denseTimeTrajectoryPrefix e n
end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
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


noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]










theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (n : ℕ) :
    (continuousPathTrajectory P hP default).map
        (denseTimeTrajectoryPrefix DenseTime.enumeration n ∘
          ContinuousPath.denseRestriction) =
      denseTimePrefixKernel P DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n := by
  let kappa := denseTimeTrajectory P hP DenseTime.enumeration
    DenseTime.castOrderEmbedding.toEmbedding
  have hback :
      (continuousPathTrajectory P hP default).map ContinuousPath.denseRestriction = kappa := by
    exact Kernel.map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
      kappa default hK
  rw [Kernel.map_comp_right]
  · rw [hback]
    exact denseTimeTrajectory_map_prefix P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding n
  · exact ContinuousPath.measurable_denseRestriction
  · exact measurable_denseTimeTrajectoryPrefix DenseTime.enumeration n
