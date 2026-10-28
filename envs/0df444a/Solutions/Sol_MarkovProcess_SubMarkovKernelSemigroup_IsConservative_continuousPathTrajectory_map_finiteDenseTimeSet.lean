-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_finiteDenseTimeSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:52:49.151239+00:00
-- url     : https://prove2.me/submissions/e2c04a15-1924-4ca9-b71a-a197ef0dc905

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
import Definitions.Def_MarkovProcess_Trajectory_FiniteMarginals
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_prefix
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_map_restrictPath
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
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/

namespace MarkovProcess



namespace FiniteOrderedTimes

































/-- Restriction of finite coordinate paths is measurable for product measurable spaces. -/
theorem measurable_restrictPath {m n : ℕ} (e : Fin m ↪o Fin n)
    {α : Type*} [MeasurableSpace α] :
    Measurable (restrictPath e : (Fin n → α) → Fin m → α) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (e i)
end FiniteOrderedTimes
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-set finite-time laws

This file reindexes the ordered finite-time kernels by finite sets of times and proves their
Mathlib-native projectivity. It does not assert or construct a projective-limit measure.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]













private noncomputable def inclusionOrderEmb {I J : Finset NNReal} (hJI : J ⊆ I) :
    Fin J.card ↪o Fin I.card :=
  (J.orderIsoOfFin rfl).toOrderEmbedding |>.trans
    (OrderEmbedding.ofStrictMono
      (fun t : J ↦ (⟨t, hJI t.property⟩ : I)) (fun _ _ h ↦ h)) |>.trans
    (I.orderIsoOfFin rfl).symm.toOrderEmbedding

private theorem finiteSetTimes_restrict {I J : Finset NNReal} (hJI : J ⊆ I) :
    (finiteSetTimes I).restrict (inclusionOrderEmb hJI) = finiteSetTimes J := by
  apply DFunLike.ext _ _
  intro i
  change (((I.orderIsoOfFin rfl)
      ((I.orderIsoOfFin rfl).symm
        ⟨↑(J.orderIsoOfFin rfl i), hJI (J.orderIsoOfFin rfl i).property⟩) : I) :
      NNReal) = ((J.orderIsoOfFin rfl i : J) : NNReal)
  rw [OrderIso.apply_symm_apply]

omit [MeasurableSpace α] in
private theorem orderedPathToFiniteSet_restrict {I J : Finset NNReal} (hJI : J ⊆ I) :
    Finset.restrict₂ (π := fun _ ↦ α) hJI ∘ orderedPathToFiniteSet (α := α) I =
      orderedPathToFiniteSet J ∘
        FiniteOrderedTimes.restrictPath (inclusionOrderEmb hJI) := by
  funext path t
  change path ((I.orderIsoOfFin rfl).symm ⟨t, hJI t.property⟩) =
    path (inclusionOrderEmb hJI ((J.orderIsoOfFin rfl).symm t))
  simp only [inclusionOrderEmb, RelEmbedding.coe_trans, Function.comp_apply,
    OrderIso.coe_toOrderEmbedding, OrderIso.apply_symm_apply]
  rfl

namespace IsConservative





/-- A finite-set kernel restricted along an inclusion is the kernel on the smaller set. -/
theorem finiteSetKernel_map_restrict₂ (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) {I J : Finset NNReal} (hJI : J ⊆ I) :
    finiteSetKernel P J =
      (finiteSetKernel P I).map (Finset.restrict₂ (π := fun _ ↦ α) hJI) := by
  rw [finiteSetKernel_eq_map, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
  · rw [orderedPathToFiniteSet_restrict hJI, Kernel.map_comp_right]
    · rw [hP.finiteTimeKernel_map_restrictPath P (finiteSetTimes I)
          (inclusionOrderEmb hJI), finiteSetTimes_restrict hJI]
    · exact FiniteOrderedTimes.measurable_restrictPath (inclusionOrderEmb hJI)
    · exact measurable_orderedPathToFiniteSet J
  · exact measurable_orderedPathToFiniteSet I
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ α) hJI
end IsConservative
end SubMarkovKernelSemigroup
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
# Finite rational-time marginals of continuous-path trajectories

This file transports the finite-dimensional laws of the canonical dense-time trajectory to
arbitrary finite sets of nonnegative rational times.  The target coordinates are indexed by the
corresponding finite set of physical `NNReal` times, exactly as in `finiteSetKernel`.

No assertion is made at irrational times or about a Markov, strong Markov, or Hunt property of
the continuous-path law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal


noncomputable section



private theorem exists_denseTimePhysicalSet_subset_prefix
    (e : ℕ ≃ DenseTime) (I : Finset DenseTime) :
    ∃ n, denseTimePhysicalSet I ⊆
      denseTimePhysicalPrefix e DenseTime.castOrderEmbedding.toEmbedding n := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro t ht
      simp only [denseTimePhysicalSet, Finset.map_empty, Finset.notMem_empty] at ht
  | @insert a I ha ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨max n (e.symm a + 1), ?_⟩
      intro t ht
      rw [denseTimePhysicalSet, Finset.mem_map] at ht
      obtain ⟨d, hd, rfl⟩ := ht
      rw [denseTimePhysicalPrefix, Finset.mem_map]
      refine ⟨d, ?_, rfl⟩
      rw [CountableEnumeration.mem_prefix_iff]
      rw [Finset.mem_insert] at hd
      rcases hd with rfl | hd
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
      · have hmem : DenseTime.castOrderEmbedding d ∈ denseTimePhysicalSet I := by
          rw [denseTimePhysicalSet, Finset.mem_map]
          exact ⟨d, hd, rfl⟩
        have hprefix := hn hmem
        rw [denseTimePhysicalPrefix, Finset.mem_map] at hprefix
        obtain ⟨d', hd', heq⟩ := hprefix
        have hdd' : d = d' := DenseTime.castOrderEmbedding.injective heq.symm
        subst d'
        rw [CountableEnumeration.mem_prefix_iff] at hd'
        exact Nat.lt_of_lt_of_le hd' (le_max_left _ _)

private noncomputable def finEquivDenseTimePhysicalPrefix
    (e : ℕ ≃ DenseTime) (n : ℕ) :
    Fin n ≃ denseTimePhysicalPrefix e DenseTime.castOrderEmbedding.toEmbedding n :=
  Equiv.ofBijective
    (fun i ↦
      ⟨DenseTime.castOrderEmbedding (e i), by
        rw [denseTimePhysicalPrefix, Finset.mem_map]
        exact ⟨e i, by
          rw [CountableEnumeration.mem_prefix_iff, e.symm_apply_apply]
          exact i.isLt, rfl⟩⟩)
    ⟨by
      intro i j hij
      apply Fin.ext
      apply e.injective
      apply DenseTime.castOrderEmbedding.injective
      exact congrArg Subtype.val hij,
    by
      intro t
      have ht := t.property
      change t.val ∈ (CountableEnumeration.prefix e n).map
        DenseTime.castOrderEmbedding.toEmbedding at ht
      rw [Finset.mem_map] at ht
      obtain ⟨d, hd, hdt⟩ := ht
      let i : Fin n := ⟨e.symm d, by
        rw [CountableEnumeration.mem_prefix_iff] at hd
        exact hd⟩
      refine ⟨i, Subtype.ext ?_⟩
      change DenseTime.castOrderEmbedding (e i) = t
      rw [show e i = d by exact e.apply_symm_apply d]
      exact hdt⟩

variable {α : Type*}

private def physicalPrefixPathOfFinPath
    (e : ℕ ≃ DenseTime) (n : ℕ) (path : Fin n → α) :
    denseTimePhysicalPrefix e DenseTime.castOrderEmbedding.toEmbedding n → α :=
  fun t ↦ path ((finEquivDenseTimePhysicalPrefix e n).symm t)

private theorem measurable_physicalPrefixPathOfFinPath
    [MeasurableSpace α] (e : ℕ ≃ DenseTime) (n : ℕ) :
    Measurable (physicalPrefixPathOfFinPath (α := α) e n) :=
  measurable_pi_iff.mpr fun t ↦
    measurable_pi_apply ((finEquivDenseTimePhysicalPrefix e n).symm t)


variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

private theorem continuousPathTrajectory_map_physicalPrefix
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (n : ℕ) :
    (continuousPathTrajectory P hP default).map
        (fun path (t : denseTimePhysicalPrefix DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n) ↦ path t) =
      finiteSetKernel P (denseTimePhysicalPrefix DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n) := by
  let equiv := finEquivDenseTimePhysicalPrefix DenseTime.enumeration n
  have hleft :
      physicalPrefixPathOfFinPath (α := alpha) DenseTime.enumeration n ∘
          (denseTimeTrajectoryPrefix DenseTime.enumeration n ∘
            ContinuousPath.denseRestriction) =
        fun path (t : denseTimePhysicalPrefix DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n) ↦ path t := by
    funext path t
    change path (DenseTime.castOrderEmbedding
      (DenseTime.enumeration (equiv.symm t))) = path t
    have heq := equiv.apply_symm_apply t
    exact congrArg path (congrArg Subtype.val heq)
  have hright :
      physicalPrefixPathOfFinPath (α := alpha) DenseTime.enumeration n ∘
          denseTimePrefixReindex DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding n = id := by
    funext path t
    change path (equiv (equiv.symm t)) = path t
    rw [equiv.apply_symm_apply]
  rw [← hleft, Kernel.map_comp_right]
  · rw [continuousPathTrajectory_map_prefix P hP default hK n,
      denseTimePrefixKernel_eq_map, ← Kernel.map_comp_right]
    · rw [hright, Kernel.map_id]
    · exact measurable_denseTimePrefixReindex DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n
    · exact measurable_physicalPrefixPathOfFinPath DenseTime.enumeration n
  · exact (measurable_denseTimeTrajectoryPrefix DenseTime.enumeration n).comp
      ContinuousPath.measurable_denseRestriction
  · exact measurable_physicalPrefixPathOfFinPath DenseTime.enumeration n


theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (I : Finset DenseTime) :
    (continuousPathTrajectory P hP default).map
        (fun path (t : denseTimePhysicalSet I) ↦ path t) =
      finiteSetKernel P (denseTimePhysicalSet I) := by
  obtain ⟨n, hsubset⟩ :=
    exists_denseTimePhysicalSet_subset_prefix DenseTime.enumeration I
  have hfun :
      (fun path : ContinuousPath alpha ↦
        fun t : denseTimePhysicalSet I ↦ path t) =
      Finset.restrict₂ (π := fun _ ↦ alpha) hsubset ∘
        (fun path : ContinuousPath alpha ↦
          fun t : denseTimePhysicalPrefix DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n ↦ path t) := by
    rfl
  rw [hfun, Kernel.map_comp_right]
  · rw [continuousPathTrajectory_map_physicalPrefix P hP default hK n]
    exact (hP.finiteSetKernel_map_restrict₂ P hsubset).symm
  · apply measurable_pi_iff.mpr
    intro t
    rw [BorelSpace.measurable_eq (α := alpha)]
    exact (ContinuousPath.continuous_eval (alpha := alpha) (t : NNReal)).borel_measurable
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hsubset
