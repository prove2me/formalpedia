-- Prove2me | solution 1 for MarkovProcess.map_finTail_pi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T01:01:51.450669+00:00
-- url     : https://prove2.me/submissions/b9fb3c50-074e-4f43-bbf3-6378c41823eb

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib
import Theorems.Thm_MarkovProcess_measurable_finTail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

/-- Source: MarkovProcess/Examples/BrownianMotion.lean:306-320, pinned commit. -/
theorem solution {n : ℕ} (nu : Fin (n + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (nu i)] :
    (Measure.pi nu).map Fin.tail = Measure.pi (fun i : Fin n ↦ nu i.succ) := by
  refine (Measure.pi_eq fun A hA ↦ ?_).symm
  have hpre : (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' (Set.univ.pi A)
      = Set.univ.pi (@Fin.cons n (fun _ ↦ Set ℝ) Set.univ A) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    rw [Fin.forall_fin_succ]
    simp [Fin.tail]
  rw [Measure.map_apply MarkovProcess.measurable_finTail (MeasurableSet.univ_pi hA), hpre, Measure.pi_pi,
    Fin.prod_univ_succ]
  simp
