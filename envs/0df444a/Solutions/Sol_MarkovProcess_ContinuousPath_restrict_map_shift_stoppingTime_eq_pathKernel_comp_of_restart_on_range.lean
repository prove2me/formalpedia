-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:34:28.597386+00:00
-- url     : https://prove2.me/submissions/cb733171-25e0-4e7a-be09-83c60db6b957

import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Theorems.Thm_MarkovProcess_ContinuousPath_coordinateProcess_apply

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurability of random shifts of continuous paths

Shifting a continuous path by a Borel measurable random time, and evaluating it at that time,
are Borel measurable, because the deterministic shift and the evaluation are jointly continuous
in the time and the path.  A finite `NNReal`-valued stopping time for the canonical filtration is
such a random time.  No countable-range premise is used.

This is ordinary measurability infrastructure.  It proves no restart identity and no conditional
expectation formula; those are in `Trajectory/FellerStoppingRestart.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Shifting by a Borel measurable random time is Borel measurable. -/
theorem measurable_shift_of_measurable (T : ContinuousPath alpha → NNReal)
    (hT : Measurable T) :
    Measurable (fun omega ↦ shift (T omega) omega) := by
  have hpair : Measurable (fun omega : ContinuousPath alpha ↦ (T omega, omega)) :=
    hT.prodMk measurable_id
  exact (continuous_shift (alpha := alpha)).measurable.comp hpair

variable [MeasurableSpace alpha] [BorelSpace alpha]





/-- Shifting by a finite stopping time for the canonical filtration is Borel measurable. -/
theorem measurable_shift_stoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable (fun omega ↦ shift (T omega) omega) :=
  measurable_shift_of_measurable T (measurable_of_isStoppingTime T hT)



end ContinuousPath
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measure-level restart at countable-range stopping times

Deterministic-time restricted restart identities at the attained times of a countable-range
finite stopping time patch to the measure-level identity at that stopping time: restricting the
path law to an event in the stopped sigma-algebra and shifting by the stopping time gives the
path kernel restarted from the state at the stopping time.  The proof decomposes the event over
the countable level sets of the stopping time.

This is ordinary conditional infrastructure.  The restart hypothesis is an assumption here; it
is proved for the continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]



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
# Measure-level restart at countable-range stopping times

Deterministic-time restricted restart identities at the attained times of a countable-range
finite stopping time patch to the measure-level identity at that stopping time: restricting the
path law to an event in the stopped sigma-algebra and shifting by the stopping time gives the
path kernel restarted from the state at the stopping time.  The proof decomposes the event over
the countable level sets of the stopping time.

This is ordinary conditional infrastructure.  The restart hypothesis is an assumption here; it
is proved for the continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal


variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution
    (Q : Kernel alpha (ContinuousPath alpha))
    (x : alpha) (tau : ContinuousPath alpha → NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (tau omega : WithTop NNReal)))
    (htauRange : (Set.range tau).Countable)
    (hRestart : ∀ S ∈ Set.range tau, ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[canonicalFiltration (alpha := alpha) S] A →
        ((Q x).restrict A).map (shift S) =
          Kernel.comap Q (coordinateProcess (alpha := alpha) S)
              (measurable_coordinateProcess S) ∘ₘ ((Q x).restrict A)) :
    ∀ A : Set (ContinuousPath alpha), MeasurableSet[htau.measurableSpace] A →
      ((Q x).restrict A).map (fun omega ↦ shift (tau omega) omega) =
        Kernel.comap Q (fun omega ↦ omega (tau omega))
            (measurable_eval_stoppingTime_borel tau htau) ∘ₘ ((Q x).restrict A) := by
  classical
  intro A hA
  have : Countable (Set.range tau) := htauRange.to_subtype
  have hcoercedRange : (Set.range fun omega ↦ (tau omega : WithTop NNReal)).Countable := by
    refine (htauRange.image (fun t : NNReal ↦ (t : WithTop NNReal))).mono ?_
    rintro i ⟨omega, rfl⟩
    exact ⟨tau omega, ⟨omega, rfl⟩, rfl⟩
  have hYmeas : Measurable (fun omega : ContinuousPath alpha ↦ shift (tau omega) omega) :=
    measurable_shift_stoppingTime tau htau
  set lev : (Set.range tau) → Set (ContinuousPath alpha) :=
    fun S ↦ A ∩ {omega | tau omega = (S : NNReal)} with hlev
  have hlevF : ∀ S : Set.range tau,
      MeasurableSet[canonicalFiltration (alpha := alpha) (S : NNReal)] (lev S) := by
    intro S
    have h1 := hA.2 ((S : NNReal))
    have h2 : MeasurableSet[canonicalFiltration (alpha := alpha) (S : NNReal)]
        {omega | (tau omega : WithTop NNReal) = ((S : NNReal) : WithTop NNReal)} :=
      htau.measurableSet_eq_of_countable_range hcoercedRange (S : NNReal)
    have hset : lev S =
        (A ∩ {omega | (tau omega : WithTop NNReal) ≤ ((S : NNReal) : WithTop NNReal)}) ∩
          {omega | (tau omega : WithTop NNReal) = ((S : NNReal) : WithTop NNReal)} := by
      ext omega
      simp only [hlev, Set.mem_inter_iff, Set.mem_ofPred_eq, WithTop.coe_eq_coe,
        WithTop.coe_le_coe]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2.le⟩, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩
    rw [hset]
    exact h1.inter h2
  have hlevAmb : ∀ S : Set.range tau, MeasurableSet (lev S) := fun S ↦
    (canonicalFiltration (alpha := alpha)).le (S : NNReal) _ (hlevF S)
  have hdisj : Pairwise (Function.onFun Disjoint lev) := by
    intro S S' hSS'
    refine Set.disjoint_left.mpr fun omega homega homega' ↦ hSS' ?_
    simp only [hlev, Set.mem_inter_iff, Set.mem_ofPred_eq] at homega homega'
    exact Subtype.ext (by rw [← homega.2, ← homega'.2])
  have hunion : ⋃ S : Set.range tau, lev S = A := by
    ext omega
    simp only [hlev, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨⟨tau omega, ⟨omega, rfl⟩⟩, h, rfl⟩⟩
  ext B hB
  rw [Measure.map_apply hYmeas hB,
    Measure.bind_apply hB (Kernel.aemeasurable _),
    Measure.restrict_apply (hYmeas hB)]
  have hLHS : ((fun omega : ContinuousPath alpha ↦ shift (tau omega) omega) ⁻¹' B) ∩ A =
      ⋃ S : Set.range tau, (((shift (S : NNReal)) ⁻¹' B) ∩ lev S) := by
    rw [← hunion]
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage, hlev, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hB', S, hA', hS⟩
      exact ⟨S, by rw [← hS]; exact hB', hA', hS⟩
    · rintro ⟨S, hB', hA', hS⟩
      exact ⟨by rw [hS]; exact hB', S, hA', hS⟩
  rw [hLHS, measure_iUnion (fun S S' hSS' ↦ ((hdisj hSS').mono
      Set.inter_subset_right Set.inter_subset_right))
    (fun S ↦ (measurable_shift_fixed (S : NNReal) hB).inter (hlevAmb S))]
  have hRHS : ∫⁻ omega, (Kernel.comap Q (fun omega ↦ omega (tau omega))
        (measurable_eval_stoppingTime_borel tau htau)) omega B ∂((Q x).restrict A) =
      ∑' S : Set.range tau, ∫⁻ omega in lev S, Q (omega (tau omega)) B ∂(Q x) := by
    simp only [Kernel.comap_apply]
    show ∫⁻ omega in A, Q (omega (tau omega)) B ∂(Q x) = _
    rw [← hunion, lintegral_iUnion hlevAmb hdisj]
  rw [hRHS]
  refine tsum_congr fun S ↦ ?_
  have hres := congrArg (fun rho : Measure (ContinuousPath alpha) ↦ rho B)
    (hRestart (S : NNReal) S.2 (lev S) (hlevF S))
  simp only [Measure.map_apply (measurable_shift_fixed (S : NNReal)) hB,
    Measure.restrict_apply (measurable_shift_fixed (S : NNReal) hB),
    Measure.bind_apply hB (Kernel.aemeasurable _), Kernel.comap_apply,
    coordinateProcess_apply] at hres
  rw [hres]
  refine setLIntegral_congr_fun (hlevAmb S) fun omega homega ↦ ?_
  simp only [hlev, Set.mem_inter_iff, Set.mem_ofPred_eq] at homega
  rw [homega.2]
