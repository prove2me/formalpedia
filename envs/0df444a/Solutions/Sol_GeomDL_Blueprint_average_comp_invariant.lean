-- Prove2me | solution 1 for GeomDL.Blueprint.average_comp_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:46:24.452961+00:00
-- url     : https://prove2.me/submissions/2bff2302-c958-4507-a74d-f24a16672f06

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

open MeasureTheory GeomDL.Blueprint

theorem solution {G Ω C : Type*} [Group G] [MulAction G Ω] [Fintype Ω]
    [MeasurableSpace G] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    [MeasurableInv G] [MeasurableSMul G Ω]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulRightInvariant] (hμ : μ ≠ 0) :
    (∀ (h : G) (x : Ω → ℝ), groupAverage μ (act h x) = groupAverage μ x) ∧
    (∀ U : (Ω → C) → (Ω → ℝ), IsEquivariant (G := G) U →
      IsInvariant (G := G) (groupAverage μ ∘ U)) := by
  have key : ∀ (h : G) (x : Ω → ℝ), groupAverage μ (act h x) = groupAverage μ x := by
    intro h x
    unfold groupAverage
    congr 1
    have hact : ∀ g : G, act g (act h x) = act (g * h) x := by
      intro g; funext u; simp [act, mul_smul]
    simp only [hact]
    have hmeas : Measurable (fun g : G => act g x) := by
      rw [measurable_pi_iff]; intro u
      exact (measurable_of_countable x).comp ((measurable_smul_const u).comp measurable_inv)
    have hmap : Measure.map (fun g : G => g * h) μ = μ := Measure.IsMulRightInvariant.map_mul_right_eq_self h
    have hae : AEMeasurable (fun g : G => g * h) μ := by
      by_contra hc
      rw [Measure.map_of_not_aemeasurable hc] at hmap
      exact hμ hmap.symm
    have := integral_map (μ := μ) hae (f := fun g : G => act g x)
      (by rw [hmap]; exact hmeas.aestronglyMeasurable)
    rw [hmap] at this
    exact this.symm
  refine ⟨key, fun U hU g x => ?_⟩
  simp only [Function.comp, hU g x, key]
