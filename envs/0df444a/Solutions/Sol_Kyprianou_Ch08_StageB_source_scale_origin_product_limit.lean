-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_origin_product_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:17:15.215024+00:00
-- url     : https://prove2.me/submissions/4e7993bd-ec87-4968-8a37-1f3007645d7e

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB Filter
open scoped Topology

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun x : ℝ => x * W 0 x * W q x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ)) := by
  have hW0cont := (source_family_positive_monotone ψ W hW 0
    (le_refl (0 : ℝ))).2.2
  have hWqcont := (source_family_positive_monotone ψ W hW q hq).2.2
  have hs : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    change 0 < x at hx
    exact hx.le
  have hto0 : Tendsto (W 0) (𝓝[>] (0 : ℝ)) (𝓝 (W 0 0)) :=
    (hW0cont 0 (by simp)).mono_left (nhdsWithin_mono _ hs)
  have htoq : Tendsto (W q) (𝓝[>] (0 : ℝ)) (𝓝 (W q 0)) :=
    (hWqcont 0 (by simp)).mono_left (nhdsWithin_mono _ hs)
  have ht : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa only [zero_mul] using (ht.mul hto0).mul htoq
