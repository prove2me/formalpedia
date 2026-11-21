-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_geometric_laplace_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:40:24.087901+00:00
-- url     : https://prove2.me/submissions/7e476de4-3155-4924-8857-2da3562ba2e0

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_laplace_gap_pos
import Theorems.Thm_AvramDividend_Classical_scale_renewal_laplace_geometric_series
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q β : ℝ) (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hroot : Phi ψ q < β) :
    (∑' n : ℕ, q ^ n * ((ψ β)⁻¹) ^ (n + 1)) =
      (ψ β - q)⁻¹ := by
  have hgap := source_scale_laplace_gap_pos ψ W hW q β hq hβ hroot
  have hψ : 0 < ψ β := lt_of_le_of_lt hq hgap
  exact AvramDividend.Classical.scale_renewal_laplace_geometric_series
    q (ψ β) hq hψ hgap
