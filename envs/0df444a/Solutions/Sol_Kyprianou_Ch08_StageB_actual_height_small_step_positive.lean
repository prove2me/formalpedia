-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actual_height_small_step_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:42:14.78794+00:00
-- url     : https://prove2.me/submissions/a45fce79-b512-4d45-b8ff-477d99356dfd

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_upper_drawdown
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_upper_integral
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_positive_from_quadratic
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponent_quadratic_upper
import Theorems.Thm_Kyprianou_Ch08_StageB_shifted_two_sided_upcrossing_eq_original
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ h : ℝ, 0 < h →
      ∃ d : ℝ, 0 < d ∧ d < h ∧
        0 < (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d h ω},
          Real.exp (Phi ψ q * d) * discountedAt q (tauPlus D.X d ω) ∂P) := by
  intro h hh
  let d : ℝ := h / 4
  let l : ℝ := h / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hl : 0 < l := by dsimp [l]; linarith
  have hdh : d < h := by dsimp [d]; linarith
  have hsum : l + d + d = h := by dsimp [l, d]; ring
  have hsubs :
      {ω | tauPlus D.X d ω < tauMinus D.X (-l) ω} ⊆
      {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω} := by
    intro ω hw
    change NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω
    intro t ht
    exact lt_of_le_of_lt
      (source_result8_2_v2_bridge_upper_drawdown P D l d hl hd t ω ht hw)
      (lt_add_of_pos_right _ hd)
  have hbridge := source_result8_2_v2_bridge_upper_integral
    P D q hq l d hl hd hsubs
  obtain ⟨K, hK, hgrowth⟩ := source_result81_exponent_quadratic_upper Ω P D ψ hψ
  have hwpos (a : ℝ) (ha : 0 < a) : 0 < W q a :=
    source_result81_scale_positive_from_quadratic ψ q (W q)
      (hW q hq) K hK hgrowth a ha
  have hratio : 0 < W q l / W q (l + d) :=
    div_pos (hwpos l hl) (hwpos (l + d) (by linarith))
  have hexit : 0 < upBeforeDownExpectation P D.X q l (l + d) := by
    rw [source_result81_upper_exit_ratio Ω P D ψ hψ W hW q l (l + d)
      hq (by linarith) (by linarith)]
    exact hratio
  have hraw :
      0 < ∫ ω, (if tauPlus D.X d ω < tauMinus D.X (-l) ω
        then discountedAt q (tauPlus D.X d ω) else 0) ∂P := by
    rw [← shifted_two_sided_upcrossing_eq_original P D.X q l d]
    exact hexit
  have hrestricted :
      0 < ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω},
        discountedAt q (tauPlus D.X d ω) ∂P :=
    lt_of_lt_of_le hraw hbridge
  refine ⟨d, hd, hdh, ?_⟩
  have hn :
      0 < ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω},
        Real.exp (Phi ψ q * d) * discountedAt q (tauPlus D.X d ω) ∂P := by
    rw [integral_const_mul]
    exact mul_pos (Real.exp_pos _) hrestricted
  simpa only [hsum] using hn
