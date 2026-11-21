-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_origin_discount_invariant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:08:39.064+00:00
-- url     : https://prove2.me/submissions/99c98d2a-e17f-44ef-a9f8-bbb64332e657

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_resolvent_positive_x
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_vanishes_origin
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_right_origin_add_vanishing_eq
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB Filter
open scoped Topology

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    W q 0 = W 0 0 := by
  have hs : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    change 0 < x at hx
    exact hx.le
  have hcq := (source_family_positive_monotone ψ W hW q hq).2.2
  have hc0 := (source_family_positive_monotone ψ W hW 0
    (le_refl (0 : ℝ))).2.2
  have htq := (hcq 0 (by simp)).mono_left (nhdsWithin_mono _ hs)
  have ht0 := (hc0 0 (by simp)).mono_left (nhdsWithin_mono _ hs)
  exact right_origin_add_vanishing_eq (W q) (W 0)
    (fun x : ℝ => ∫ s in Set.Ioc (0 : ℝ) x,
       W 0 s * W q (x - s) ∂volume) q htq ht0
    (source_scale_convolution_vanishes_origin ψ W hW q hq)
    (fun x hx => source_scale_resolvent_positive_x ψ W hW q x hq hx)
