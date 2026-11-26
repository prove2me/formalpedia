-- Prove2me | solution 1 for Kyprianou.Ch04.boundedFiniteSupportMemLpV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:07:44.676751+00:00
-- url     : https://prove2.me/submissions/447c5c28-03eb-4697-9f96-28c02a7d8129

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

/-- Bounded measurable kernels supported on a finite-measure set are integrable and square-integrable. -/
theorem solution {A : Type} [MeasurableSpace A]
    (μ : Measure A) (S : Set A) (hS : MeasurableSet S) (hfin : μ S < ⊤)
    (g : A → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ p, ‖g p‖ ≤ C)
    (hsupp : ∀ p, p ∉ S → g p = 0) :
    Integrable g μ ∧ MemLp g 2 μ := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa [Measure.restrict_apply_univ] using hfin⟩
  have heq : S.indicator g = g := by
    funext x
    by_cases h : x ∈ S
    · simp [h]
    · simp [h,hsupp x h]
  have hp (p : ENNReal) : MemLp g p (μ.restrict S) :=
    MemLp.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hb)
  exact ⟨memLp_one_iff_integrable.mp (heq ▸ (memLp_indicator_iff_restrict hS).mpr (hp 1)),
    heq ▸ (memLp_indicator_iff_restrict hS).mpr (hp 2)⟩
