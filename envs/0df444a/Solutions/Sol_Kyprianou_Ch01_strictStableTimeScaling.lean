-- Prove2me | solution 1 for Kyprianou.Ch01.strictStableTimeScaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:43:21.722195+00:00
-- url     : https://prove2.me/submissions/90d6f772-baca-4111-895b-bf76eb541609

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (alpha : ℝ)
    (ha0 : 0 < alpha) (ha2 : alpha < 2)
    (hX : IsLevyProcess X P)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (Psi : ℝ → ℂ)
    (hchar : ∀ (t : ℝ≥0) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (-((t : ℝ) : ℂ) * Psi xi))
    (hhomog : ∀ c : ℝ, 0 < c → ∀ xi : ℝ,
      Psi (c * xi) = ((c ^ alpha : ℝ) : ℂ) * Psi xi) :
    ∀ (scale t : ℝ≥0), 0 < scale →
      P.map (X (scale * t)) =
        P.map (fun ω => (scale : ℝ) ^ (1 / alpha) * X t ω) := by
  intro scale t hs
  let c : ℝ := (scale : ℝ) ^ (1 / alpha)
  have hsreal : 0 < (scale : ℝ) := by exact_mod_cast hs
  have hc : 0 < c := Real.rpow_pos_of_pos hsreal _
  have hc_pow : c ^ alpha = (scale : ℝ) := by
    dsimp [c]
    rw [← Real.rpow_mul (le_of_lt hsreal)]
    have hmul : (1 / alpha) * alpha = (1 : ℝ) := by
      field_simp [ne_of_gt ha0]
    rw [hmul, Real.rpow_one]
  apply Measure.ext_of_charFun
  funext xi
  have hsFun : (fun ω => (scale : ℝ) ^ (1 / alpha) * X t ω) =
       fun ω => c * X t ω := by rfl
  rw [hsFun]
  rw [charFun_map_mul_comp (hXmeas t).aemeasurable c xi]
  rw [hchar (scale * t) xi, hchar t (c * xi)]
  rw [hhomog c hc xi, hc_pow]
  congr 1
  push_cast
  ring
