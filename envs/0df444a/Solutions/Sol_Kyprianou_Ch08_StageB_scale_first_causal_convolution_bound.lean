-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.scale_first_causal_convolution_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:02:56.781818+00:00
-- url     : https://prove2.me/submissions/db67d854-3a87-4a87-9d1c-2d75f3de9809

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_scale_causal_integrand_upper
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB
open scoped ENNReal

theorem solution (W : ℝ → ℝ)
    (hmono : MonotoneOn W (Set.Ici (0 : ℝ)))
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ W t)
    (x : ℝ) (hx : 0 ≤ x)
    (hint : IntegrableOn (fun s : ℝ => W s * W (x - s))
      (Set.Ioc (0 : ℝ) x) volume) :
    (∫ s in Set.Ioc (0 : ℝ) x, W s * W (x - s) ∂volume) ≤
      x * (W x) ^ 2 := by
  have hf : Integrable (fun s : ℝ => W s * W (x - s))
      (volume.restrict (Set.Ioc (0 : ℝ) x)) := hint
  have hfinite : volume (Set.Ioc (0 : ℝ) x) ≠ ∞ := by
    simp [Real.volume_Ioc]
  have hg : Integrable (fun _ : ℝ => (W x) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) x)) := by
    exact integrableOn_const (μ := volume)
      (s := Set.Ioc (0 : ℝ) x) (hs := hfinite)
  have hle : (∫ s in Set.Ioc (0 : ℝ) x, W s * W (x - s) ∂volume) ≤
      (∫ _ : ℝ in Set.Ioc (0 : ℝ) x, (W x)^2 ∂volume) := by
    apply integral_mono_ae hf hg
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact scale_causal_integrand_upper W hmono hpos x s hx hs.1.le hs.2
  have hconst : (∫ _ : ℝ in Set.Ioc (0 : ℝ) x, (W x)^2 ∂volume) =
      x * (W x)^2 := by
    simp [setIntegral_const, Real.volume_Ioc, hx]
  simpa only [hconst] using hle
