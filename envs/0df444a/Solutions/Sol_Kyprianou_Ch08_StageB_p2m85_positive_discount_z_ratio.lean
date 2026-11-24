-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_positive_discount_z_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:46:56.308573+00:00
-- url     : https://prove2.me/submissions/ee5af701-1991-4964-8ab5-96a2a7a115c5

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_tilted_scale_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_derivative_exact
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_exp_convolution_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_exp_convolution_substitution
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun z : ℝ => Zscale q (W q) z / W q z)
      atTop (𝓝 (q / Phi ψ q)) := by
  let φ := Phi ψ q
  let L := deriv (Phi ψ) q
  let f (z : ℝ) := Real.exp (-φ*z) * W q z
  have hw := hW q hq.le
  have hroot := hw.1.2.1
  have hz : ψ 0 = 0 := by
    simpa [SpectrallyNegativeModel.toData] using (hψ 0 1 le_rfl (by norm_num)).2
  have hφ : 0 < φ := by
    by_contra hn
    have he : φ = 0 := le_antisymm (le_of_not_gt hn) hroot.1
    have h := hroot.2
    change ψ φ = q at h
    rw [he,hz] at h
    exact hq.ne h
  obtain ⟨hm, hl⟩ := p2m89_tilted_scale_limit D ψ W hψ hW q hq
  obtain ⟨hp, hd⟩ := p2m89_phi_derivative_exact D ψ W hψ hW q hq
  have hL : L ≠ 0 := by dsimp [L]; rw [hd]; exact inv_ne_zero hp.ne'
  have hconv := p2m85_exp_convolution_limit f φ L hφ hm.measurable
    (fun t => mul_nonneg (Real.exp_nonneg _) (hw.2.2.1 t)) (hm.ge_of_tendsto hl) hl
  have hi : Tendsto (fun z => Real.exp (-φ*z) * ∫ y in (0 : ℝ)..z, W q y)
      atTop (𝓝 (L/φ)) := by
    apply hconv.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact p2m85_exp_convolution_substitution (W q) φ z hz hw.2.1
  have hex : Tendsto (fun z : ℝ => Real.exp (-φ*z)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
      (show -φ < 0 from neg_lt_zero.mpr hφ))
  have hnum := hex.add (hi.const_mul q)
  rw [zero_add] at hnum
  have hquot := hnum.div hl hL
  have he : q * (L/φ) / L = q/φ := by field_simp [hL, hφ.ne']
  rw [he] at hquot
  apply hquot.congr'
  apply Eventually.of_forall
  intro z
  change (Real.exp (-φ*z) + q*(Real.exp (-φ*z) * ∫ y in (0 : ℝ)..z, W q y)) /
    (Real.exp (-φ*z)*W q z) = _
  rw [show Real.exp (-φ*z) + q*(Real.exp (-φ*z) * ∫ y in (0 : ℝ)..z, W q y) =
    Real.exp (-φ*z) * Zscale q (W q) z by unfold Zscale; ring]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)
