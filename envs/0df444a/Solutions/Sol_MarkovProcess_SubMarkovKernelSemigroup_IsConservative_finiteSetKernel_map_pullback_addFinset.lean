-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteSetKernel_map_pullback_addFinset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:15:19.414891+00:00
-- url     : https://prove2.me/submissions/37a18ed7-94e9-4744-8933-ad4f189ea8b4

import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteSetKernel_map_pullback_translate

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Translation of finite-set kernels

This file translates finite sets of nonnegative observation times, reindexes paths on the
translated set back to the original coordinates, and proves the corresponding translation law
for conservative transition-kernel semigroups.  It is finite-dimensional kernel infrastructure;
it does not assert a path-space Markov property.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section













theorem measurable_pullbackFiniteSetTranslate {alpha : Type*} [MeasurableSpace alpha]
    (s : NNReal) (I : Finset NNReal) :
    Measurable (pullbackFiniteSetTranslate (alpha := alpha) s I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply (finiteSetTranslateEquiv s I t)







namespace IsConservative

variable {alpha : Type*} [MeasurableSpace alpha]



end IsConservative

end
end SubMarkovKernelSemigroup

namespace DenseTime

/-- Casting a translated finite dense-time set to physical time agrees with translating its
finite set of physical times. -/
theorem map_castOrderEmbedding_addFinset (s : DenseTime) (I : Finset DenseTime) :
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

end DenseTime
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Translation of finite dense-time kernels

This file transports the finite-set kernel translation law from physical nonnegative-real times
to finite sets of dense times, using the canonical coordinate reindexings.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

namespace IsConservative

variable {alpha : Type*} [MeasurableSpace alpha]



end IsConservative

end
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
# Translation of finite dense-time kernels

This file transports the finite-set kernel translation law from physical nonnegative-real times
to finite sets of dense times, using the canonical coordinate reindexings.
-/

open MeasureTheory ProbabilityTheory




variable {alpha : Type*} [MeasurableSpace alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
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
    DenseTime.map_castOrderEmbedding_addFinset s I
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
    · rw [hP.finiteSetKernel_map_pullback_translate P, Kernel.map_comp]
    · exact measurable_pullbackFiniteSetTranslate
        (DenseTime.castOrderEmbedding s) (denseTimePhysicalSet I)
    · exact DenseTimePath.measurable_pullbackPhysicalSet I
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hsubset
  · exact (DenseTimePath.measurable_pullbackPhysicalSet I).comp
      (measurable_pullbackFiniteSetTranslate
        (DenseTime.castOrderEmbedding s) (denseTimePhysicalSet I))
