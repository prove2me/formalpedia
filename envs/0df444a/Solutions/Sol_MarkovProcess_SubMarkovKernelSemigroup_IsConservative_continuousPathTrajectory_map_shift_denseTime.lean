-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_shift_denseTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T23:27:06.839092+00:00
-- url     : https://prove2.me/submissions/413fbc0b-cb0e-462a-890d-b209ce1efbcb

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
import Definitions.Def_MarkovProcess_V3H_Kernel_FiniteRestrictionIdentification_619c5320
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
# Shifts of dense-time paths

This file defines addition by a nonnegative rational time on the fixed dense carrier and the
induced shift of dense-time paths.  Restriction of a continuous path commutes with this shift.
No probability law or Markov property is asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option autoImplicit false

namespace MarkovProcess

noncomputable section

namespace DenseTime







end DenseTime

namespace DenseTimePath

variable {alpha : Type*}

private theorem p2m_inline_shift_apply (s t : DenseTime) (path : DenseTime → alpha) :
    shift s path t = path (s + t) := rfl











variable [MeasurableSpace alpha]



end DenseTimePath

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Restricting a path after a rational physical-time shift is the same as shifting its
dense-time restriction. -/
theorem denseRestriction_shift (s : DenseTime) (omega : ContinuousPath alpha) :
    denseRestriction
        (shift (DenseTime.castOrderEmbedding s) omega) =
      DenseTimePath.shift s (denseRestriction omega) := by
  funext t
  simp only [denseRestriction_apply, shift_apply, DenseTimePath.p2m_inline_shift_apply,
    DenseTime.castOrderEmbedding_add]

end ContinuousPath
end
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-coordinate shifts on dense-time paths

Addition by a dense time transports finite sets of dense-time coordinates injectively.  This file
provides the resulting coordinate equivalence and relates restriction after shifting a dense-time
path to restriction on the translated finite set.  It makes no probability-law or Markov claim.
-/

namespace MarkovProcess

noncomputable section

namespace DenseTime









end DenseTime

namespace DenseTimePath

variable {alpha : Type*}





variable [MeasurableSpace alpha]

/-- Reindexing from a translated finite dense-time set is measurable. -/
theorem measurable_pullbackAddFinset (s : DenseTime) (I : Finset DenseTime) :
    Measurable (pullbackAddFinset (alpha := alpha) s I) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_pi_apply (DenseTime.addFinsetEquiv s I t)

omit [MeasurableSpace alpha] in
/-- Restriction after shifting equals translated restriction followed by the canonical
reindexing. -/
theorem restrict_shift (s : DenseTime) (I : Finset DenseTime) (path : DenseTime → alpha) :
    I.restrict (shift s path) =
      pullbackAddFinset s I ((DenseTime.addFinset s I).restrict path) := by
  funext t
  rfl

end DenseTimePath
end
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Rational-time shifts of continuous trajectory laws

The canonical continuous trajectory kernel restarts after every nonnegative rational time.  The
proof first identifies all finite rational-coordinate marginals of the shifted path and then uses
uniqueness on the dense product path space and injectivity of dense restriction.  This is an
unconditional law identity; conditional and strong Markov statements require additional work.
-/

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


open MeasureTheory ProbabilityTheory
namespace MarkovProcess
variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]
  [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

private theorem p2m_inline_map_denseRestriction_injective :
    Function.Injective
      (fun kappa : Kernel beta (ContinuousPath alpha) ↦
        kappa.map ContinuousPath.denseRestriction) := by
  intro kappa eta h
  ext x s hs
  have himage : MeasurableSet (ContinuousPath.denseRestriction '' s) :=
    ContinuousPath.measurableEmbedding_denseRestriction.measurableSet_image' hs
  have hx := congrArg
    (fun z : Kernel beta (DenseTime → alpha) ↦
      z x (ContinuousPath.denseRestriction '' s)) h
  dsimp only at hx
  rw [Kernel.map_apply' _ ContinuousPath.measurable_denseRestriction x himage,
    Kernel.map_apply' _ ContinuousPath.measurable_denseRestriction x himage] at hx
  simpa only [ContinuousPath.denseRestriction_injective.preimage_image] using hx
end MarkovProcess

namespace MarkovProcess
variable {index alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]

private theorem p2m_inline_eq_of_map_finiteRestriction_eq
    (kappa eta : Kernel beta (index → alpha)) [IsFiniteKernel kappa]
    (h : ∀ I : Finset index,
      kappa.map I.restrict = eta.map I.restrict) :
    kappa = eta := by
  ext x : 1
  let family : (I : Finset index) → Measure (I → alpha) :=
    fun I ↦ (kappa x).map I.restrict
  have hkappa : IsProjectiveLimit (kappa x) family := by
    intro I
    rfl
  have heta : IsProjectiveLimit (eta x) family := by
    intro I
    have hx := congrArg (fun z : Kernel beta (I → alpha) ↦ z x) (h I)
    simpa only [Kernel.map_apply _ (Finset.measurable_restrict I) x] using hx.symm
  let (I : Finset index) : IsFiniteMeasure (family I) := by
    dsimp only [family]
    infer_instance
  exact hkappa.unique heta
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
# Rational-time shifts of continuous trajectory laws

The canonical continuous trajectory kernel restarts after every nonnegative rational time.  The
proof first identifies all finite rational-coordinate marginals of the shifted path and then uses
uniqueness on the dense product path space and injectivity of dense restriction.  This is an
unconditional law identity; conditional and strong Markov statements require additional work.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup
private theorem p2m_inline_finiteSetTranslateEquiv_apply (s : NNReal) (I : Finset NNReal) (t : I) :
    (finiteSetTranslateEquiv s I t : NNReal) = s + t :=
  rfl

private theorem p2m_inline_measurable_pullbackFiniteSetTranslate {alpha : Type*} [MeasurableSpace alpha]
    (s : NNReal) (I : Finset NNReal) :
    Measurable (pullbackFiniteSetTranslate (alpha := alpha) s I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply (finiteSetTranslateEquiv s I t)

private def finiteSetTranslateFinOrderIso (s : NNReal) (I : Finset NNReal) :
    Fin I.card ≃o Fin (finiteSetTranslate s I).card :=
  Fin.castOrderIso (by simp only [finiteSetTranslate, Finset.card_map])

private theorem finiteSetTimes_translate (s : NNReal) (I : Finset NNReal) :
    (finiteSetTimes (finiteSetTranslate s I)).restrict
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding =
      (finiteSetTimes I).translate s := by
  let e := (finiteSetTranslateFinOrderIso s I).toOrderEmbedding
  have hcard : (finiteSetTranslate s I).card = I.card := by
    simp only [finiteSetTranslate, Finset.card_map]
  have hleft :
      (fun i : Fin I.card ↦ finiteSetTimes (finiteSetTranslate s I) (e i)) =
        (finiteSetTranslate s I).orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      exact Finset.orderEmbOfFin_mem _ rfl (e i)
    · exact (finiteSetTimes (finiteSetTranslate s I)).strictMono.comp e.strictMono
  have hright :
      (fun i : Fin I.card ↦ s + finiteSetTimes I i) =
        (finiteSetTranslate s I).orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      exact Finset.mem_map_of_mem (addLeftEmbedding s)
        (Finset.orderEmbOfFin_mem I rfl i)
    · intro i j hij
      simpa only [add_comm] using add_lt_add_left ((finiteSetTimes I).strictMono hij) s
  apply DFunLike.ext _ _
  intro i
  exact congrFun (hleft.trans hright.symm) i

private theorem pullback_orderedPathToFiniteSet {alpha : Type*}
    (s : NNReal) (I : Finset NNReal) :
    pullbackFiniteSetTranslate (alpha := alpha) s I ∘
        orderedPathToFiniteSet (α := alpha) (finiteSetTranslate s I) =
      orderedPathToFiniteSet I ∘ FiniteOrderedTimes.restrictPath
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding := by
  funext path t
  apply congrArg path
  apply (finiteSetTimes (finiteSetTranslate s I)).injective
  have hshifted :
      finiteSetTimes (finiteSetTranslate s I)
          (((finiteSetTranslate s I).orderIsoOfFin rfl).symm
            (finiteSetTranslateEquiv s I t)) =
        s + t := by
    change (((finiteSetTranslate s I).orderIsoOfFin rfl
      (((finiteSetTranslate s I).orderIsoOfFin rfl).symm
        (finiteSetTranslateEquiv s I t)) : finiteSetTranslate s I) : NNReal) = s + t
    rw [OrderIso.apply_symm_apply]
    exact p2m_inline_finiteSetTranslateEquiv_apply s I t
  have htimes := congrArg
    (fun times : FiniteOrderedTimes I.card ↦
      times ((I.orderIsoOfFin rfl).symm t))
    (finiteSetTimes_translate s I)
  have horiginal : finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) = t := by
    change (((I.orderIsoOfFin rfl) ((I.orderIsoOfFin rfl).symm t) : I) : NNReal) = t
    exact congrArg Subtype.val ((I.orderIsoOfFin rfl).apply_symm_apply t)
  change finiteSetTimes (finiteSetTranslate s I)
      ((finiteSetTranslateFinOrderIso s I).toOrderEmbedding
        ((I.orderIsoOfFin rfl).symm t)) =
    s + finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) at htimes
  rw [horiginal] at htimes
  rw [hshifted]
  exact htimes.symm
end MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.DenseTime
private theorem p2m_inline_map_castOrderEmbedding_addFinset (s : DenseTime) (I : Finset DenseTime) :
    (addFinset s I).map castOrderEmbedding.toEmbedding =
      SubMarkovKernelSemigroup.finiteSetTranslate (castOrderEmbedding s)
        (I.map castOrderEmbedding.toEmbedding) := by
  ext t
  simp only [addFinset, SubMarkovKernelSemigroup.finiteSetTranslate, Finset.mem_map]
  constructor
  · rintro ⟨u, ⟨r, hrI, rfl⟩, rfl⟩
    exact ⟨castOrderEmbedding r, ⟨r, hrI, rfl⟩, (castOrderEmbedding_add s r).symm⟩
  · rintro ⟨u, ⟨r, hrI, hru⟩, hut⟩
    subst u
    exact ⟨s + r, ⟨r, hrI, rfl⟩, (castOrderEmbedding_add s r).trans hut⟩
end MarkovProcess.DenseTime

namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

private theorem p2m_inline_exists_denseTimePhysicalSet_subset_prefix
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

private noncomputable def p2m_inline_finEquivDenseTimePhysicalPrefix
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

variable {α : Type*} [MeasurableSpace α]

private noncomputable def p2m_inline_physicalPrefixPathOfFinPath
    (e : ℕ ≃ DenseTime) (n : ℕ) (path : Fin n → α) :
    denseTimePhysicalPrefix e DenseTime.castOrderEmbedding.toEmbedding n → α :=
  fun t ↦ path ((p2m_inline_finEquivDenseTimePhysicalPrefix e n).symm t)

private theorem p2m_inline_measurable_physicalPrefixPathOfFinPath
    [MeasurableSpace α] (e : ℕ ≃ DenseTime) (n : ℕ) :
    Measurable (p2m_inline_physicalPrefixPathOfFinPath (α := α) e n) :=
  measurable_pi_iff.mpr fun t ↦
    measurable_pi_apply ((p2m_inline_finEquivDenseTimePhysicalPrefix e n).symm t)

private theorem p2m_inline_continuousPathTrajectory_map_prefix
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

private theorem p2m_inline_continuousPathTrajectory_map_physicalPrefix
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
  let equiv := p2m_inline_finEquivDenseTimePhysicalPrefix DenseTime.enumeration n
  have hleft :
      p2m_inline_physicalPrefixPathOfFinPath (α := alpha) DenseTime.enumeration n ∘
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
      p2m_inline_physicalPrefixPathOfFinPath (α := alpha) DenseTime.enumeration n ∘
          denseTimePrefixReindex DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding n = id := by
    funext path t
    change path (equiv (equiv.symm t)) = path t
    rw [equiv.apply_symm_apply]
  rw [← hleft, Kernel.map_comp_right]
  · rw [p2m_inline_continuousPathTrajectory_map_prefix P hP default hK n,
      denseTimePrefixKernel_eq_map, ← Kernel.map_comp_right]
    · rw [hright, Kernel.map_id]
    · exact measurable_denseTimePrefixReindex DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n
    · exact p2m_inline_measurable_physicalPrefixPathOfFinPath DenseTime.enumeration n
  · exact (measurable_denseTimeTrajectoryPrefix DenseTime.enumeration n).comp
      ContinuousPath.measurable_denseRestriction
  · exact p2m_inline_measurable_physicalPrefixPathOfFinPath DenseTime.enumeration n

private theorem p2m_inline_continuousPathTrajectory_map_finiteDenseTimeSet
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
    p2m_inline_exists_denseTimePhysicalSet_subset_prefix DenseTime.enumeration I
  have hfun :
      (fun path : ContinuousPath alpha ↦
        fun t : denseTimePhysicalSet I ↦ path t) =
      Finset.restrict₂ (π := fun _ ↦ alpha) hsubset ∘
        (fun path : ContinuousPath alpha ↦
          fun t : denseTimePhysicalPrefix DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n ↦ path t) := by
    rfl
  rw [hfun, Kernel.map_comp_right]
  · rw [p2m_inline_continuousPathTrajectory_map_physicalPrefix P hP default hK n]
    exact (hP.finiteSetKernel_map_restrict₂ P hsubset).symm
  · apply measurable_pi_iff.mpr
    intro t
    rw [BorelSpace.measurable_eq (α := alpha)]
    exact (ContinuousPath.continuous_eval (alpha := alpha) (t : NNReal)).borel_measurable
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hsubset

private theorem p2m_inline_continuousPathTrajectory_map_denseRestriction_map_restrict
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
      rw [p2m_inline_continuousPathTrajectory_map_finiteDenseTimeSet P hP default hK I]
    · exact hEvaluate
    · exact DenseTimePath.measurable_pullbackPhysicalSet I
  · exact ContinuousPath.measurable_denseRestriction
  · exact Finset.measurable_restrict I

variable {α : Type*} [MeasurableSpace α]

private theorem p2m_inline_fin_orderEmbedding_self_eq_id {n : ℕ} (e : Fin n ↪o Fin n) :
    e = (OrderIso.refl (Fin n)).toOrderEmbedding := by
  let eo : Fin n ≃o Fin n :=
    { Equiv.ofBijective e ⟨e.injective, Finite.surjective_of_injective e.injective⟩ with
      map_rel_iff' := e.le_iff_le }
  apply DFunLike.ext _ _
  intro i
  apply Fin.ext
  exact Fin.coe_orderIso_apply eo i

private theorem p2m_inline_exists_factor_succAboveOrderEmb {m n : ℕ} (e : Fin m ↪o Fin (n + 1)) (h : m ≤ n) :
    ∃ (p : Fin (n + 1)) (d : Fin m ↪o Fin n), d.trans (Fin.succAboveOrderEmb p) = e := by
  classical
  have hns : ¬ Function.Surjective e := by
    intro he
    have hcard := Fintype.card_le_of_surjective e he
    simp only [Fintype.card_fin] at hcard
    exact (Nat.not_succ_le_self n) (hcard.trans h)
  rw [Function.Surjective] at hns
  push Not at hns
  obtain ⟨p, hp⟩ := hns
  by_cases plast : p = Fin.last n
  · have hlast : ∀ i, e i ≠ Fin.last n := by
      intro i
      simpa only [plast] using hp i
    let d : Fin m ↪o Fin n :=
      OrderEmbedding.ofStrictMono
        (fun i ↦ (e i).castPred (hlast i))
        (Fin.strictMono_castPred_comp hlast e.strictMono)
    refine ⟨p, d, ?_⟩
    apply DFunLike.ext _ _
    intro i
    change Fin.succAbove p ((e i).castPred (hlast i)) = e i
    rw [plast, Fin.succAbove_last_apply, Fin.castSucc_castPred]
  · let q : Fin n := p.castPred plast
    have hqp : q.castSucc = p := Fin.castSucc_castPred p plast
    have havoid : ∀ i, e i ≠ q.castSucc := by
      intro i
      rw [hqp]
      exact hp i
    have hmono : StrictMono (fun i ↦ q.predAbove (e i)) := by
      intro i j hij
      rw [← (Fin.succAboveOrderEmb p).lt_iff_lt]
      simpa only [Fin.succAboveOrderEmb_apply, ← hqp,
        Fin.succAbove_predAbove (havoid i), Fin.succAbove_predAbove (havoid j)] using
        e.strictMono hij
    let d : Fin m ↪o Fin n :=
      OrderEmbedding.ofStrictMono (fun i ↦ q.predAbove (e i)) hmono
    refine ⟨p, d, ?_⟩
    apply DFunLike.ext _ _
    intro i
    change Fin.succAbove p (q.predAbove (e i)) = e i
    rw [← hqp, Fin.succAbove_predAbove (havoid i)]

variable {W X Y Z : Type*}
variable [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

private theorem p2m_inline_compProd_prodMkLeft_comp (κ : Kernel X Y) (η : Kernel Y Z)
    (ξ : Kernel W X) [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ξ] :
    (κ.comp ξ) ⊗ₖ Kernel.prodMkLeft W η = (κ ⊗ₖ Kernel.prodMkLeft X η).comp ξ := by
  rw [Kernel.compProd_prodMkLeft_eq_comp, Kernel.compProd_prodMkLeft_eq_comp,
    Kernel.comp_assoc]

private theorem p2m_inline_finiteTimeKernel_translate (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (s : NNReal) {n : ℕ} (times : FiniteOrderedTimes n) :
    finiteTimeKernel P (times.translate s) = (finiteTimeKernel P times).comp (P s) := by
  induction n with
  | zero =>
      let : IsMarkovKernel (P s) := hP.isMarkovKernel s
      rw [finiteTimeKernel_zero, finiteTimeKernel_zero, Kernel.const_comp']
  | succ n ih =>
      let : IsFiniteKernel (P s) := (P.isSubMarkovKernel s).isFiniteKernel
      let : IsFiniteKernel (P (times 0)) :=
        (P.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
        hP.isMarkovKernel_finiteTimeKernel P times.relativeTail
      rw [finiteTimeKernel_succ, finiteTimeKernel_succ]
      simp only [FiniteOrderedTimes.translate_apply, FiniteOrderedTimes.relativeTail_translate]
      rw [P.add s (times 0), Kernel.mapOfMeasurable_eq_map,
        Kernel.mapOfMeasurable_eq_map, p2m_inline_compProd_prodMkLeft_comp, Kernel.map_comp]

private theorem p2m_inline_finiteTimeKernel_map_restrictPath
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    {m n : ℕ} (times : FiniteOrderedTimes n) (e : Fin m ↪o Fin n) :
    (finiteTimeKernel P times).map (FiniteOrderedTimes.restrictPath e) =
      finiteTimeKernel P (times.restrict e) := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by
        have hcard := Fintype.card_le_of_injective e e.injective
        simpa only [Fintype.card_fin, Nat.le_zero] using hcard
      subst m
      rw [p2m_inline_fin_orderEmbedding_self_eq_id e]
      rw [show (FiniteOrderedTimes.restrictPath (OrderIso.refl (Fin 0)).toOrderEmbedding :
            (Fin 0 → α) → Fin 0 → α) = id by
          funext path
          exact FiniteOrderedTimes.restrictPath_id path]
      rw [Kernel.map_id, FiniteOrderedTimes.restrict_id]
  | succ n ih =>
      have hcard : m ≤ n + 1 := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
      by_cases hm : m = n + 1
      · subst m
        rw [p2m_inline_fin_orderEmbedding_self_eq_id e]
        rw [show (FiniteOrderedTimes.restrictPath
              (OrderIso.refl (Fin (n + 1))).toOrderEmbedding :
              (Fin (n + 1) → α) → Fin (n + 1) → α) = id by
            funext path
            exact FiniteOrderedTimes.restrictPath_id path]
        rw [Kernel.map_id, FiniteOrderedTimes.restrict_id]
      · have hmn : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hcard hm)
        obtain ⟨p, d, hd⟩ := p2m_inline_exists_factor_succAboveOrderEmb e hmn
        rw [← hd]
        have hdelete := hP.finiteTimeKernel_map_restrictPath_succAbove P times p
        have hdel : Measurable (FiniteOrderedTimes.restrictPath
            (Fin.succAboveOrderEmb p) : (Fin (n + 1) → α) → Fin n → α) :=
          FiniteOrderedTimes.measurable_restrictPath (Fin.succAboveOrderEmb p)
        have hdmeas : Measurable
            (FiniteOrderedTimes.restrictPath d : (Fin n → α) → Fin m → α) :=
          FiniteOrderedTimes.measurable_restrictPath d
        rw [show (FiniteOrderedTimes.restrictPath (d.trans (Fin.succAboveOrderEmb p)) :
              (Fin (n + 1) → α) → Fin m → α) =
            FiniteOrderedTimes.restrictPath d ∘
              FiniteOrderedTimes.restrictPath (Fin.succAboveOrderEmb p) by rfl]
        rw [Kernel.map_comp_right _ hdel hdmeas, hdelete,
          ih (times.restrict (Fin.succAboveOrderEmb p)) d,
          FiniteOrderedTimes.restrict_trans]

private theorem p2m_inline_finiteSetKernel_map_pullback_translate
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (s : NNReal) (I : Finset NNReal) :
    (finiteSetKernel P (finiteSetTranslate s I)).map
        (pullbackFiniteSetTranslate (alpha := alpha) s I) =
      (finiteSetKernel P I).comp (P s) := by
  rw [finiteSetKernel_eq_map, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
  · rw [pullback_orderedPathToFiniteSet, Kernel.map_comp_right]
    · rw [p2m_inline_finiteTimeKernel_map_restrictPath P hP
          (finiteSetTimes (finiteSetTranslate s I))
          (finiteSetTranslateFinOrderIso s I).toOrderEmbedding,
        finiteSetTimes_translate, p2m_inline_finiteTimeKernel_translate P hP s,
        Kernel.map_comp]
    · exact FiniteOrderedTimes.measurable_restrictPath
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding
    · exact measurable_orderedPathToFiniteSet I
  · exact measurable_orderedPathToFiniteSet (finiteSetTranslate s I)
  · exact p2m_inline_measurable_pullbackFiniteSetTranslate s I

private theorem p2m_inline_finiteSetKernel_map_pullback_addFinset
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (s : DenseTime) (I : Finset DenseTime) :
    (finiteSetKernel P (denseTimePhysicalSet (DenseTime.addFinset s I))).map
        (DenseTimePath.pullbackAddFinset s I ∘
          DenseTimePath.pullbackPhysicalSet (DenseTime.addFinset s I)) =
      ((finiteSetKernel P (denseTimePhysicalSet I)).map
        (DenseTimePath.pullbackPhysicalSet I)).comp
        (P (DenseTime.castOrderEmbedding s)) := by
  have hsets :
      denseTimePhysicalSet (DenseTime.addFinset s I) =
        finiteSetTranslate (DenseTime.castOrderEmbedding s) (denseTimePhysicalSet I) :=
    DenseTime.p2m_inline_map_castOrderEmbedding_addFinset s I
  have hsubset :
      finiteSetTranslate (DenseTime.castOrderEmbedding s) (denseTimePhysicalSet I) ⊆
        denseTimePhysicalSet (DenseTime.addFinset s I) :=
    hsets.symm.le
  have hcoordinates :
      DenseTimePath.pullbackAddFinset (alpha := alpha) s I ∘
          DenseTimePath.pullbackPhysicalSet (DenseTime.addFinset s I) =
        (DenseTimePath.pullbackPhysicalSet I ∘
          pullbackFiniteSetTranslate (DenseTime.castOrderEmbedding s)
            (denseTimePhysicalSet I)) ∘
          Finset.restrict₂ (π := fun _ ↦ alpha) hsubset := by
    funext path t
    apply congrArg path
    apply Subtype.ext
    exact DenseTime.castOrderEmbedding_add s t
  rw [hcoordinates, Kernel.map_comp_right]
  · rw [← hP.finiteSetKernel_map_restrict₂ P hsubset, Kernel.map_comp_right]
    · rw [p2m_inline_finiteSetKernel_map_pullback_translate P hP, Kernel.map_comp]
    · exact p2m_inline_measurable_pullbackFiniteSetTranslate
        (DenseTime.castOrderEmbedding s) (denseTimePhysicalSet I)
    · exact DenseTimePath.measurable_pullbackPhysicalSet I
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hsubset
  · exact (DenseTimePath.measurable_pullbackPhysicalSet I).comp
      (p2m_inline_measurable_pullbackFiniteSetTranslate
        (DenseTime.castOrderEmbedding s) (denseTimePhysicalSet I))
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
    (s : DenseTime) :
    (continuousPathTrajectory P hP default).map
        (ContinuousPath.shift (DenseTime.castOrderEmbedding s)) =
      (continuousPathTrajectory P hP default).comp
        (P (DenseTime.castOrderEmbedding s)) := by
  apply MarkovProcess.p2m_inline_map_denseRestriction_injective
  apply MarkovProcess.p2m_inline_eq_of_map_finiteRestriction_eq
  intro I
  have hShift :=
    ContinuousPath.measurable_shift_fixed (alpha := alpha) (DenseTime.castOrderEmbedding s)
  have hDense := ContinuousPath.measurable_denseRestriction (alpha := alpha)
  have hRestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) I
  have hRestrictAdd :=
    Finset.measurable_restrict (X := fun _ ↦ alpha) (DenseTime.addFinset s I)
  have hPullback := DenseTimePath.measurable_pullbackAddFinset (alpha := alpha) s I
  have hleft :
      I.restrict ∘ (ContinuousPath.denseRestriction (alpha := alpha) ∘
          ContinuousPath.shift (alpha := alpha) (DenseTime.castOrderEmbedding s)) =
        DenseTimePath.pullbackAddFinset (alpha := alpha) s I ∘
          ((DenseTime.addFinset s I).restrict ∘
            ContinuousPath.denseRestriction (alpha := alpha)) := by
    funext omega
    change
      I.restrict (ContinuousPath.denseRestriction
        (ContinuousPath.shift (DenseTime.castOrderEmbedding s) omega)) =
        DenseTimePath.pullbackAddFinset s I
          ((DenseTime.addFinset s I).restrict (ContinuousPath.denseRestriction omega))
    rw [ContinuousPath.denseRestriction_shift]
    exact DenseTimePath.restrict_shift s I (ContinuousPath.denseRestriction omega)
  let Q := continuousPathTrajectory P hP default
  calc
    (((Q.map (ContinuousPath.shift (DenseTime.castOrderEmbedding s))).map
          ContinuousPath.denseRestriction).map I.restrict) =
        Q.map (I.restrict ∘ (ContinuousPath.denseRestriction ∘
          ContinuousPath.shift (DenseTime.castOrderEmbedding s))) := by
      rw [← Kernel.map_comp_right
          (Q.map (ContinuousPath.shift (DenseTime.castOrderEmbedding s))) hDense hRestrict,
        ← Kernel.map_comp_right Q hShift (hRestrict.comp hDense)]
      rw [Function.comp_assoc]
    _ = Q.map (DenseTimePath.pullbackAddFinset s I ∘
          ((DenseTime.addFinset s I).restrict ∘ ContinuousPath.denseRestriction)) := by
      rw [hleft]
    _ = (((Q.map ContinuousPath.denseRestriction).map
          (DenseTime.addFinset s I).restrict).map
            (DenseTimePath.pullbackAddFinset s I)) := by
      rw [← Function.comp_assoc,
        Kernel.map_comp_right Q hDense (hPullback.comp hRestrictAdd),
        Kernel.map_comp_right (Q.map ContinuousPath.denseRestriction) hRestrictAdd hPullback]
    _ = ((finiteSetKernel P (denseTimePhysicalSet (DenseTime.addFinset s I))).map
          (DenseTimePath.pullbackPhysicalSet (DenseTime.addFinset s I))).map
            (DenseTimePath.pullbackAddFinset s I) := by
      rw [p2m_inline_continuousPathTrajectory_map_denseRestriction_map_restrict P hP default hK]
    _ = (finiteSetKernel P (denseTimePhysicalSet (DenseTime.addFinset s I))).map
          (DenseTimePath.pullbackAddFinset s I ∘
            DenseTimePath.pullbackPhysicalSet (DenseTime.addFinset s I)) := by
      rw [Kernel.map_comp_right _
        (DenseTimePath.measurable_pullbackPhysicalSet (alpha := alpha)
          (DenseTime.addFinset s I)) hPullback]
    _ = ((finiteSetKernel P (denseTimePhysicalSet I)).map
          (DenseTimePath.pullbackPhysicalSet I)).comp
            (P (DenseTime.castOrderEmbedding s)) :=
      p2m_inline_finiteSetKernel_map_pullback_addFinset P hP s I
    _ = ((Q.map ContinuousPath.denseRestriction).map I.restrict).comp
          (P (DenseTime.castOrderEmbedding s)) := by
      rw [p2m_inline_continuousPathTrajectory_map_denseRestriction_map_restrict P hP default hK]
    _ = (((Q.comp (P (DenseTime.castOrderEmbedding s))).map
          ContinuousPath.denseRestriction).map I.restrict) := by
      rw [Kernel.map_comp, Kernel.map_comp]
