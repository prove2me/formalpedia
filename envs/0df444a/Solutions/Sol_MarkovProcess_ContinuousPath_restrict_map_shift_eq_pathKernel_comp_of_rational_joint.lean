-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.restrict_map_shift_eq_pathKernel_comp_of_rational_joint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:47:55.338865+00:00
-- url     : https://prove2.me/submissions/556dea52-9c2a-46d8-b33d-9f83304c9ba4

import Definitions.Def_MarkovProcess_V3H_Path_DenseFiltration_62a9879d
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestrictedRestart_3bd46ae7
import Definitions.Def_MarkovProcess_V3H_Restart_RestrictedRestartOfJoint_e84e7ad8
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Theorems.Thm_MarkovProcess_restrict_map_eq_comap_comp_of_map_prodMk_eq_compProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Restricted restart at rational times

This file turns a full joint-law factorization of the rational past and shifted future into the
event-restricted restart identity on the canonical continuous-path filtration.  The joint-law
factorization remains an explicit input; proving it from the finite-dimensional Markov laws is the
next process-construction step.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]









end
end ContinuousPath
end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Restricted restart at rational times

This file turns a full joint-law factorization of the rational past and shifted future into the
event-restricted restart identity on the canonical continuous-path filtration.  The joint-law
factorization remains an explicit input; proving it from the finite-dimensional Markov laws is the
next process-construction step.
-/

open MeasureTheory ProbabilityTheory



variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]







namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (x : alpha) (S : DenseTime)
    (hJoint :
      (Q x).map (fun omega ↦
          (densePastRestriction S omega,
            shift (DenseTime.castOrderEmbedding S) omega)) =
        ((Q x).map (densePastRestriction S)) ⊗ₘ
          Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S)) :
    ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[canonicalFiltration (alpha := alpha)
        (DenseTime.castOrderEmbedding S)] A →
        ((Q x).restrict A).map (shift (DenseTime.castOrderEmbedding S)) =
          Kernel.comap Q
              (coordinateProcess (alpha := alpha) (DenseTime.castOrderEmbedding S))
              (measurable_coordinateProcess (DenseTime.castOrderEmbedding S)) ∘ₘ
            ((Q x).restrict A) := by
  have hPast : Measurable (densePastRestriction (alpha := alpha) S) := by
    apply Measurable.of_comap_le
    rw [comap_densePastRestriction_eq_canonicalFiltration]
    exact (canonicalFiltration (alpha := alpha)).le (DenseTime.castOrderEmbedding S)
  have hRestricted := restrict_map_eq_comap_comp_of_map_prodMk_eq_compProd
    (Q x) (densePastRestriction S) hPast
    (shift (DenseTime.castOrderEmbedding S))
    (measurable_shift_fixed (DenseTime.castOrderEmbedding S))
    (Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S)) hJoint
  intro A hA
  have hA' : MeasurableSet[
      MeasurableSpace.comap (densePastRestriction (alpha := alpha) S) inferInstance] A := by
    rw [comap_densePastRestriction_eq_canonicalFiltration]
    exact hA
  have hKernel :
      (Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S)).comap
          (densePastRestriction S) hPast =
        Kernel.comap Q
          (coordinateProcess (alpha := alpha) (DenseTime.castOrderEmbedding S))
          (measurable_coordinateProcess (DenseTime.castOrderEmbedding S)) := by
    rw [← Kernel.comap_comp_right Q hPast (measurable_densePastTerminal S)]
    congr 1
  rw [← hKernel]
  exact hRestricted A hA'
