-- Prove2me | solution 1 for Kyprianou.Ch04.integrableIffFiniteSignedParts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:47.596034+00:00
-- url     : https://prove2.me/submissions/fb248c16-6459-44d8-92a6-9a361138c1a7

import Mathlib.MeasureTheory.Function.L1Space.Integrable
open MeasureTheory Filter
open scoped ENNReal Classical
set_option autoImplicit false

/-- Integrability is equivalent to finiteness of both signed parts. -/
theorem solution {E : Type} [MeasurableSpace E]
    (mu : Measure E) (f : E → Real) (hf : Measurable f) :
    Integrable f mu ↔
      (∫⁻ z, ENNReal.ofReal (max (f z) 0) ∂mu) < ⊤ ∧
      (∫⁻ z, ENNReal.ofReal (max (-f z) 0) ∂mu) < ⊤ := by
  let p (z : E) := max (f z) 0
  let n (z : E) := max (-f z) 0
  have hpm : Measurable p := hf.max measurable_const
  have hnm : Measurable n := hf.neg.max measurable_const
  have hpn (z : E) : 0 ≤ p z := le_max_right _ _
  have hnn (z : E) : 0 ≤ n z := le_max_right _ _
  have hsplit : f = fun z => p z - n z := by
    funext z
    dsimp [p, n]
    by_cases h : 0 ≤ f z
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · have h' := le_of_lt (lt_of_not_ge h)
      rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h'), zero_sub, neg_neg]
  have hfinite (k : E → Real) (hk : Measurable k) (hn : ∀ z, 0 ≤ k z) :
      Integrable k mu ↔ (∫⁻ z, ENNReal.ofReal (k z) ∂mu) < ⊤ :=
    ⟨fun hi => (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).1 hi.2,
      fun hi => ⟨hk.aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).2 hi⟩⟩
  change Integrable f mu ↔
    (∫⁻ z, ENNReal.ofReal (p z) ∂mu) < ⊤ ∧
    (∫⁻ z, ENNReal.ofReal (n z) ∂mu) < ⊤
  rw [← hfinite p hpm hpn, ← hfinite n hnm hnn]
  constructor
  · intro hi
    refine ⟨hi.norm.mono' hpm.aestronglyMeasurable ?_,
      hi.norm.mono' hnm.aestronglyMeasurable ?_⟩
    · exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hpn z)]
        exact max_le (le_abs_self _) (abs_nonneg _)
    · exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn z)]
        exact max_le (neg_le_abs _) (abs_nonneg _)
  · rintro ⟨hp, hn⟩
    rw [hsplit]
    exact hp.sub hn
