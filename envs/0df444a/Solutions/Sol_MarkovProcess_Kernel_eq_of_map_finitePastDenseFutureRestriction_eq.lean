-- Prove2me | solution 1 for MarkovProcess.Kernel.eq_of_map_finitePastDenseFutureRestriction_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:52:07.311969+00:00
-- url     : https://prove2.me/submissions/d30da737-9019-4b2d-bd2f-fccb657b25d5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Kernel_FiniteRestrictionIdentification_619c5320
import Definitions.Def_MarkovProcess_V3H_Restart_FinitePastRestart_281c4f1c
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Theorems.Thm_MarkovProcess_Kernel_eq_of_map_finiteRestriction_eq

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying joint laws of a finite past and a continuous future

A kernel whose values consist of a finite-coordinate past and a continuous future path is
determined by all finite coordinate marginals which retain coordinates from both pieces.  This is
the uniqueness step needed to upgrade finite-dimensional restart identities to a whole-future
joint-law factorization.  It does not assert that any particular stochastic process has those
finite-dimensional identities.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {index alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]





private def finitePastContinuousFuture
    (default : ContinuousPath alpha) (z : index ⊕ DenseTime → alpha) :
    (index → alpha) × ContinuousPath alpha :=
  (fun i ↦ z (Sum.inl i),
    ContinuousPath.continuousExtension default (fun t ↦ z (Sum.inr t)))

private theorem measurable_finitePastContinuousFuture (default : ContinuousPath alpha) :
    Measurable (finitePastContinuousFuture (index := index) (alpha := alpha) default) := by
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (Sum.inl i)
  · exact ContinuousPath.measurable_continuousExtension default |>.comp
      (measurable_pi_iff.mpr fun t ↦ measurable_pi_apply (Sum.inr t))

omit [MeasurableSpace alpha] [BorelSpace alpha]
  [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)] in
private theorem finitePastContinuousFuture_comp_finitePastDenseFuture
    (default : ContinuousPath alpha) :
    finitePastContinuousFuture (index := index) default ∘
        finitePastDenseFuture (index := index) (alpha := alpha) = id := by
  funext z
  apply Prod.ext
  · funext i
    rfl
  · exact ContinuousPath.continuousExtension_denseRestriction default z.2



end
end Kernel
end MarkovProcess


open MarkovProcess
open MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying joint laws of a finite past and a continuous future

A kernel whose values consist of a finite-coordinate past and a continuous future path is
determined by all finite coordinate marginals which retain coordinates from both pieces.  This is
the uniqueness step needed to upgrade finite-dimensional restart identities to a whole-future
joint-law factorization.  It does not assert that any particular stochastic process has those
finite-dimensional identities.
-/

open MeasureTheory ProbabilityTheory



variable {index alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]











namespace MarkovProcess.Kernel

end MarkovProcess.Kernel
open MarkovProcess.Kernel
theorem solution
    (default : ContinuousPath alpha)
    (kappa eta : Kernel beta ((index → alpha) × ContinuousPath alpha))
    [IsFiniteKernel kappa]
    (h : ∀ I : Finset (index ⊕ DenseTime),
      kappa.map (I.restrict ∘ finitePastDenseFuture) =
        eta.map (I.restrict ∘ finitePastDenseFuture)) :
    kappa = eta := by
  have hDense :
      kappa.map finitePastDenseFuture = eta.map finitePastDenseFuture := by
    apply eq_of_map_finiteRestriction_eq
    intro I
    rw [← Kernel.map_comp_right kappa measurable_finitePastDenseFuture
        (Finset.measurable_restrict I),
      ← Kernel.map_comp_right eta measurable_finitePastDenseFuture
        (Finset.measurable_restrict I)]
    exact h I
  calc
    kappa = (kappa.map finitePastDenseFuture).map
        (finitePastContinuousFuture (index := index) default) := by
      rw [← Kernel.map_comp_right]
      · rw [finitePastContinuousFuture_comp_finitePastDenseFuture, Kernel.map_id]
      · exact measurable_finitePastDenseFuture
      · exact measurable_finitePastContinuousFuture default
    _ = (eta.map finitePastDenseFuture).map
        (finitePastContinuousFuture (index := index) default) := by rw [hDense]
    _ = eta := by
      rw [← Kernel.map_comp_right]
      · rw [finitePastContinuousFuture_comp_finitePastDenseFuture, Kernel.map_id]
      · exact measurable_finitePastDenseFuture
      · exact measurable_finitePastContinuousFuture default
