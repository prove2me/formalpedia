-- Prove2me | solution 1 for Kyprianou.Ch04.finiteRandomIntegralSplitAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:17:42.137785+00:00
-- url     : https://prove2.me/submissions/81baf49a-521c-49a2-9b1c-427d3665320a

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- Finite signed-part masses justify pathwise integrability and subtraction. -/
theorem solution {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (R : Omega → Measure E) (f : Omega → E → ℝ)
    (hf : ∀ w, Measurable (f w))
    (hP : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal (max (f w z) 0) ∂(R w)) P)
    (hN : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal (max (-f w z) 0) ∂(R w)) P)
    (hp : (∫⁻ w, ∫⁻ z, ENNReal.ofReal (max (f w z) 0) ∂(R w) ∂P) < ⊤)
    (hn : (∫⁻ w, ∫⁻ z, ENNReal.ofReal (max (-f w z) 0) ∂(R w) ∂P) < ⊤) :
    ∀ᵐ w ∂P, Integrable (f w) (R w) ∧
      (∫ z, f w z ∂(R w)) =
        (∫ z, max (f w z) 0 ∂(R w)) - ∫ z, max (-f w z) 0 ∂(R w) := by
  filter_upwards [ae_lt_top' hP hp.ne, ae_lt_top' hN hn.ne] with w hwP hwN
  have hIp : Integrable (fun z => max (f w z) 0) (R w) :=
    ⟨((hf w).max measurable_const).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => le_max_right _ _)).2 hwP⟩
  have hIn : Integrable (fun z => max (-f w z) 0) (R w) :=
    ⟨((hf w).neg.max measurable_const).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => le_max_right _ _)).2 hwN⟩
  have he : (fun z => max (f w z) 0 - max (-f w z) 0) = f w := by
    funext z
    by_cases hz : 0 ≤ f w z
    · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz), sub_zero]
    · rw [max_eq_right (le_of_not_ge hz), max_eq_left (neg_nonneg.mpr (le_of_not_ge hz))]
      ring
  refine ⟨he ▸ hIp.sub hIn, ?_⟩
  exact (congrArg (fun g : E → ℝ => ∫ z, g z ∂(R w)) he.symm).trans
    (integral_sub hIp hIn)
