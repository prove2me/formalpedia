-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_convolution_small_interval_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:56:50.944973+00:00
-- url     : https://prove2.me/submissions/9e02f321-e436-4665-8f20-b743b4836e1a

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB
open scoped ENNReal

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x)
    (hi : IntegrableOn (fun s : ℝ => W 0 s * W q (x - s))
      (Set.Ioc (0 : ℝ) x) volume) :
    0 ≤ (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume) ∧
    (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume) ≤
      x * W 0 x * W q x := by
  rcases source_family_positive_monotone ψ W hW 0 (le_refl (0 : ℝ)) with
    ⟨hpos0,hmono0,_⟩
  rcases source_family_positive_monotone ψ W hW q hq with
    ⟨hposq,hmonoq,_⟩
  have hlo : 0 ≤ (∫ s in Set.Ioc (0 : ℝ) x,
      W 0 s * W q (x - s) ∂volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [] with s
    exact mul_nonneg (hpos0 s) (hposq (x - s))
  have hfinite : volume (Set.Ioc (0 : ℝ) x) ≠ ∞ := by
    simp [Real.volume_Ioc]
  have hic : IntegrableOn (fun _ : ℝ => W 0 x * W q x)
      (Set.Ioc (0 : ℝ) x) volume :=
    integrableOn_const (μ := volume) (s := Set.Ioc (0 : ℝ) x) (hs := hfinite)
  have hle : (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume) ≤
      (∫ _ : ℝ in Set.Ioc (0 : ℝ) x, W 0 x * W q x ∂volume) := by
    apply integral_mono_ae hi hic
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hxs : 0 ≤ x - s := sub_nonneg.mpr hs.2
    have h1 := hmono0 hs.1.le hx hs.2
    have h2 := hmonoq hxs hx (sub_le_self x hs.1.le)
    exact mul_le_mul h1 h2 (hposq (x - s)) (hpos0 x)
  constructor
  · exact hlo
  · calc
      (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume) ≤
        (∫ _ : ℝ in Set.Ioc (0 : ℝ) x, W 0 x * W q x ∂volume) := hle
      _ = x * W 0 x * W q x := by
        simp [setIntegral_const, Real.volume_Ioc, hx]
        ring
