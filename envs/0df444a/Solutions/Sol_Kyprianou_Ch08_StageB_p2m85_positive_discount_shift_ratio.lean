-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_positive_discount_shift_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:03:59.804803+00:00
-- url     : https://prove2.me/submissions/5337e964-6380-4ead-a05d-a8f1ce29868b

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_tilted_scale_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_derivative_exact
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q x : ℝ) (hq : 0 < q) :
    Tendsto (fun a : ℝ => W q (a-x) / W q a)
      atTop (𝓝 (Real.exp (-Phi ψ q * x))) := by
  let f (a : ℝ) := Real.exp (-Phi ψ q * a) * W q a
  have hlim : Tendsto f atTop (𝓝 (deriv (Phi ψ) q)) :=
    (p2m89_tilted_scale_limit D ψ W hψ hW q hq).2
  obtain ⟨hp, hd⟩ := p2m89_phi_derivative_exact D ψ W hψ hW q hq
  have hL : deriv (Phi ψ) q ≠ 0 := by rw [hd]; exact inv_ne_zero hp.ne'
  have ha : Tendsto (fun a : ℝ => a - x) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      tendsto_atTop_add_const_right atTop (-x) tendsto_id
  have h := (hlim.comp ha).div hlim hL
  have h' := h.const_mul (Real.exp (-Phi ψ q * x))
  rw [div_self hL, mul_one] at h'
  apply h'.congr'
  apply Eventually.of_forall
  intro a
  change Real.exp (-Phi ψ q * x) *
    ((Real.exp (-Phi ψ q * (a-x)) * W q (a-x)) /
      (Real.exp (-Phi ψ q * a) * W q a)) = _
  have he : Real.exp (-Phi ψ q * x) * Real.exp (-Phi ψ q * (a-x)) =
      Real.exp (-Phi ψ q * a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_div_assoc, ← mul_assoc, he, mul_div_mul_left _ _ (Real.exp_ne_zero _)]
