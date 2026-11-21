-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_discount_series_real_positive_x
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:11:53.608991+00:00
-- url     : https://prove2.me/submissions/b7890f30-30c6-4a7a-9672-bc69dd0a9632

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_real_series_continuous_nonnegative
import Theorems.Thm_Kyprianou_Ch08_StageB_source_real_series_laplace_premises
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hx : 0 < x) (hq : 0 ≤ q) :
    W q x = ∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x := by
  have hreg := source_real_series_continuous_nonnegative ψ W hW q hq
  obtain ⟨b,hlap⟩ := source_real_series_laplace_premises ψ W hW q hq
  obtain ⟨hposq,_,hcontq⟩ := source_family_positive_monotone ψ W hW q hq
  have hcontq' : ContinuousOn (W q) (Set.Ioi (0 : ℝ)) :=
    hcontq.mono (by intro y hy; change 0 < y at hy; exact hy.le)
  apply AvramDividend.Classical.continuousOn_Ioi_eq_of_laplace_eq
    (W q) (fun y : ℝ => ∑' n : ℕ,
      q ^ n * scaleConvolutionPower (W 0) n y) b
    hcontq' hreg.1 (fun y _ => hposq y) hreg.2
  · intro θ hθ
    obtain ⟨hz,hrq,hSint,hSlap⟩ := hlap θ hθ
    have hqtransform := ((hW q hq).2.2.2.2.2 θ hz hrq)
    refine ⟨hqtransform.1, ?_, ?_⟩
    · simpa only [neg_mul] using hSint
    · apply hqtransform.2.trans
      simpa only [neg_mul] using hSlap.symm
  · exact hx
