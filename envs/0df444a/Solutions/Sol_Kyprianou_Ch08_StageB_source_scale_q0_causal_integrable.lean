-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_q0_causal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:10:38.153735+00:00
-- url     : https://prove2.me/submissions/d35edce7-a5b3-4dbd-978d-e42e9acc7019

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_causal_reflected_product_integrable_of_weighted
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    IntegrableOn (fun s : ℝ => W 0 s * W q (x - s))
      (Set.Ioc (0 : ℝ) x) volume := by
  let β : ℝ := max 0 (Phi ψ q) + 1
  have hβ : 0 ≤ β := by
    dsimp [β]
    linarith [le_max_left (0 : ℝ) (Phi ψ q)]
  have hroot : Phi ψ q < β := by
    dsimp [β]
    linarith [le_max_right (0 : ℝ) (Phi ψ q)]
  have hint := ((hW q hq).2.2.2.2.2 β hβ hroot).1
  have hcont := (source_family_positive_monotone ψ W hW 0
    (le_refl (0 : ℝ))).2.2
  exact causal_reflected_product_integrable_of_weighted
    (W q) (W 0) β x hx (by simpa only [neg_mul] using hint) hcont
