-- Prove2me | solution 1 for Kyprianou.Ch01.positiveIntegral_of_ae_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T11:29:14.667295+00:00
-- url     : https://prove2.me/submissions/fded69b2-7ad4-477f-8840-c21a49f1ac97

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hi : Integrable f P)
    (hp : ∀ᵐ ω ∂P, 0 < f ω) :
    0 < ∫ ω, f ω ∂P := by
  have hn : ∀ᵐ ω ∂P, 0 ≤ f ω := hp.mono (fun _ h => le_of_lt h)
  apply (integral_pos_iff_support_of_nonneg_ae hn hi).2
  by_contra hbad
  have hzero : P {ω | f ω ≠ 0} = 0 :=
    le_antisymm (le_of_not_gt hbad) bot_le
  have he : f =ᵐ[P] fun _ => 0 := (ae_iff).2 hzero
  have hfalse : ∀ᵐ ω ∂P, False := by
    filter_upwards [hp, he] with ω hpos hz
    exact (ne_of_gt hpos) hz
  have hμ : P (Set.univ : Set Ω) = 0 := by
    have hh := (ae_iff).1 hfalse
    simpa using hh
  exact zero_ne_one (hμ.symm.trans measure_univ)
