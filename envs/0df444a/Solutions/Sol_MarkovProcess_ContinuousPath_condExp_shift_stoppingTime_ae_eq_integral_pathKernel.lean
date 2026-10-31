-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.condExp_shift_stoppingTime_ae_eq_integral_pathKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:56:26.312494+00:00
-- url     : https://prove2.me/submissions/506d1f57-2864-4812-a86f-ec1a86c1fb7a

import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Theorems.Thm_MarkovProcess_ContinuousPath_condExp_shift_stoppingTime_ae_eq_integral_pathKernel_of_restart_on_range

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional restart at countable-valued stopping times

This file upgrades deterministic-time conditional restart identities to a finite-valued or,
more generally, countable-valued finite stopping time.  It is ordinary conditional probability
infrastructure: the deterministic-time restart identity is a hypothesis here, proved for the
continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

noncomputable section

variable {alpha E : Type*} [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]









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
# Conditional restart at countable-valued stopping times

This file upgrades deterministic-time conditional restart identities to a finite-valued or,
more generally, countable-valued finite stopping time.  It is ordinary conditional probability
infrastructure: the deterministic-time restart identity is a hypothesis here, proved for the
continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/

open MeasureTheory ProbabilityTheory



variable {alpha E : Type*} [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]







namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (x : alpha) (tau : ContinuousPath alpha → NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (tau omega : WithTop NNReal)))
    (htauRange : (Set.range tau).Countable)
    (hRestart : ∀ (S : NNReal) (A : Set (ContinuousPath alpha)),
      MeasurableSet[canonicalFiltration (alpha := alpha) S] A →
        ((Q x).restrict A).map (shift S) =
          Kernel.comap Q (coordinateProcess (alpha := alpha) S)
              (measurable_coordinateProcess S) ∘ₘ ((Q x).restrict A))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (Q x)[fun omega ↦ F (shift (tau omega) omega)|htau.measurableSpace] =ᵐ[Q x]
      fun omega ↦ ∫ eta, F eta ∂Q (omega (tau omega)) := by
  exact condExp_shift_stoppingTime_ae_eq_integral_pathKernel_of_restart_on_range
    Q x tau htau htauRange (fun S _ ↦ hRestart S) F hF C hFC
