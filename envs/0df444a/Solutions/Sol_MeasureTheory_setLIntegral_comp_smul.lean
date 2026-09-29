-- Prove2me | solution 1 for MeasureTheory.setLIntegral_comp_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T06:07:48.275261+00:00
-- url     : https://prove2.me/submissions/f2bf43c7-74e2-4ba5-9489-26723d7cc1e9

import Mathlib

open MeasureTheory Set

open scoped Pointwise

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    (g : E → ENNReal) (S : Set E) (r : ℝ) (hr : r ≠ 0) :
    ∫⁻ w in S, g (r • w) ∂mu
      = ENNReal.ofReal |r ^ Module.finrank ℝ E|⁻¹ * ∫⁻ y in r • S, g y ∂mu := by
  classical
  set R : E ≃ᵐ E :=
    (Homeomorph.smul (isUnit_iff_ne_zero.2 hr).unit).toMeasurableEquiv with hRdef
  have hRapp : ∀ w : E, R w = r • w := fun w => rfl
  have hpre : R ⁻¹' (r • S) = S := by
    ext w
    simp only [Set.mem_preimage, hRapp]
    constructor
    · rintro ⟨v, hv, hveq⟩
      have : v = w := smul_right_injective E hr hveq
      exact this ▸ hv
    · intro hw; exact ⟨w, hw, rfl⟩
  have hmap : Measure.map R (mu.restrict (R ⁻¹' (r • S)))
      = (Measure.map R mu).restrict (r • S) := (R.restrict_map mu (r • S)).symm
  have key : ∫⁻ y in r • S, g y ∂(Measure.map R mu)
      = ∫⁻ w in S, g (r • w) ∂mu := by
    rw [← hmap, MeasureTheory.lintegral_map_equiv g R, hpre]
    rfl
  have hRfun : (⇑R) = (fun x : E => r • x) := rfl
  rw [← key, hRfun, Measure.map_addHaar_smul mu hr,
    MeasureTheory.setLIntegral_smul_measure]
  rw [abs_inv]
  rfl
