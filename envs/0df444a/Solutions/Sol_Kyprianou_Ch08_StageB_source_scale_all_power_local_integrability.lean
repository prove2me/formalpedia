-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_all_power_local_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:16:08.000337+00:00
-- url     : https://prove2.me/submissions/7c2e0a02-9a8e-43c6-89a7-f003fa5a9f2c

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_weighted_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_causal_reflected_product_integrable_of_weighted
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) :
    ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      IntegrableOn
        (fun s : ℝ => W 0 s * scaleConvolutionPower (W 0) n (x - s))
        (Set.Ioc (0 : ℝ) x) volume := by
  intro n x hx
  let β : ℝ := max 0 (Phi ψ 0) + 1
  have hβ : 0 ≤ β := by
    dsimp [β]
    linarith [le_max_left (0 : ℝ) (Phi ψ 0)]
  have hroot : Phi ψ 0 < β := by
    dsimp [β]
    linarith [le_max_right (0 : ℝ) (Phi ψ 0)]
  have hWcont : ContinuousOn (W 0) (Set.Ici (0 : ℝ)) :=
    (source_family_positive_monotone ψ W hW 0 (le_refl (0 : ℝ))).2.2
  have hweighted := (source_scale_power_weighted_integrable ψ W hW β hβ hroot) n
  apply causal_reflected_product_integrable_of_weighted
    (scaleConvolutionPower (W 0) n) (W 0) β x hx
    (by simpa only [neg_mul] using hweighted) hWcont
