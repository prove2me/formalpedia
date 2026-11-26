-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49ExpClockNonmeasurableV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:49:24.911941+00:00
-- url     : https://prove2.me/submissions/724c03f4-122a-48ae-a927-d4c1fee66166

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    [MeasurableSpace (ULift.{0} ℝ)]
    (hS : ∀ S : Set (ULift.{0} ℝ), MeasurableSet S ↔ S.Countable ∨ Sᶜ.Countable) :
    ∃ a : ULift.{0} ℝ → NNReal, (∀ e, 0 < a e) ∧
      ¬ MeasurableSet {e | a e ≤ 1} := by
  let a (e : ULift.{0} ℝ) : NNReal := ⟨Real.exp e.down,(Real.exp_pos _).le⟩
  refine ⟨a,fun e => Real.exp_pos e.down,?_⟩
  intro h
  let S : Set (ULift.{0} ℝ) := {e | a e ≤ 1}
  have hcut (e : ULift.{0} ℝ) : e ∈ S ↔ e.down ≤ 0 := by
    change Real.exp e.down ≤ (1 : ℝ) ↔ _
    rw [← Real.exp_zero,Real.exp_le_exp]
  rcases (hS S).mp h with hc | hc
  · let f : ℝ → ULift.{0} ℝ := fun x => ULift.up (-Real.exp x)
    have hi : Function.Injective f := by
      intro x y he
      have H := congrArg ULift.down he
      exact Real.exp_strictMono.injective (neg_inj.mp H)
    have he : f ⁻¹' S = (Set.univ : Set ℝ) := by
      ext x
      simp only [Set.mem_preimage,Set.mem_univ,iff_true,hcut]
      exact (neg_nonpos.mpr (Real.exp_pos x).le)
    exact Set.not_countable_univ (he ▸ hc.preimage hi)
  · let f : ℝ → ULift.{0} ℝ := fun x => ULift.up (Real.exp x)
    have hi : Function.Injective f := by
      intro x y he
      exact Real.exp_strictMono.injective (congrArg ULift.down he)
    have he : f ⁻¹' Sᶜ = (Set.univ : Set ℝ) := by
      ext x
      simp only [Set.mem_preimage,Set.mem_compl_iff,Set.mem_univ,iff_true,hcut]
      exact not_le_of_gt (Real.exp_pos x)
    exact Set.not_countable_univ (he ▸ hc.preimage hi)
