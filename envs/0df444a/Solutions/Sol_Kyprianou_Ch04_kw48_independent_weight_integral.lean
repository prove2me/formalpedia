-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_independent_weight_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:31:45.212712+00:00
-- url     : https://prove2.me/submissions/906403f6-d7c4-480d-bf55-0e44a26982fa

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

/-- Independence from a sub-sigma-algebra factorises the integral
of a transformed future increment times a measurable past weight. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (G : Ω → Real) (W : Ω → Complex) (phi : Real → Complex)
    (hG : @Measurable Ω Real mΩ inferInstance G)
    (hW : @Measurable Ω Complex m inferInstance W)
    (hphi : Measurable phi)
    (hind : Indep (MeasurableSpace.comap G inferInstance) m P) :
    (∫ w, phi (G w) * W w ∂P) =
      (∫ w, phi (G w) ∂P) * (∫ w, W w ∂P) := by
  have hIF : IndepFun G W P := by
    apply (IndepFun_iff_Indep G W P).2
    intro U V hU hV
    exact hind U V hU (hW.comap_le V hV)
  have hWamb : @Measurable Ω Complex mΩ inferInstance W := hW.mono hm le_rfl
  have h := (hIF.comp hphi measurable_id).integral_mul_eq_mul_integral
    (hphi.comp hG).aestronglyMeasurable hWamb.aestronglyMeasurable
  simpa only [Pi.mul_apply,Function.comp_def,id_eq] using h
