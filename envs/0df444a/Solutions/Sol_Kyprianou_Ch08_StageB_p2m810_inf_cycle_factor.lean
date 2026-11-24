-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_inf_cycle_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:28:03.202957+00:00
-- url     : https://prove2.me/submissions/1153ac1e-898e-4aa7-8ac6-6e495b5b313a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_scale_slope_nonnegative
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_lower_exit_arbitrary_scale
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_exit_payoff_mass
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_reset_quotient_algebra
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit renewal reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ ε b : ℝ, 0 < ε → 0 < b → x ≤ b →
      let A := fun y : ℝ => upBeforeDownExpectation P D.X q (y+ε) (b+ε)
      let B := fun y : ℝ => downBeforeUpExpectation P D.X q (y+ε) (b+ε)
      0 < A 0 ∧ B 0 < 1 ∧ 0 ≤ B x ∧
      A x + B x * (A 0 / (1-B 0)) =
        (Zscale q (W q) (x+ε) - W q (x+ε) *
          ((Zscale q (W q) ε - 1) / W q ε)) /
        (Zscale q (W q) (b+ε) - W q (b+ε) *
          ((Zscale q (W q) ε - 1) / W q ε)) := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa ε b he hb hxb
  dsimp only
  have hbe : 0 < b+ε := add_pos hb he
  have h0 : 0 < W q ε :=
    (p2m810_scale_slope_nonnegative Ω P D ψ W hψ hW q 0 ε hq he le_rfl he.le).1
  have hw : 0 < W q (b+ε) :=
    (p2m810_scale_slope_nonnegative Ω P D ψ W hψ hW q 0 (b+ε) hq hbe le_rfl hbe.le).1
  have hA0 := source_result81_upper_exit_ratio Ω P D ψ hψ W hW q ε (b+ε) hq hbe (by linarith)
  have hAx := source_result81_upper_exit_ratio Ω P D ψ hψ W hW q (x+ε) (b+ε) hq hbe (by linarith)
  have hB0 := p2m810_lower_exit_arbitrary_scale Ω P D ψ W hψ hW q ε (b+ε) hq hbe he.le (by linarith)
  have hBx := p2m810_lower_exit_arbitrary_scale Ω P D ψ W hψ hW q (x+ε) (b+ε) hq hbe (by linarith) (by linarith)
  have hm0 := p2m810_exit_payoff_mass Ω P D ψ W hψ hW q ε (b+ε) hq hbe he.le (by linarith)
  have hmx := p2m810_exit_payoff_mass Ω P D ψ W hψ hW q (x+ε) (b+ε) hq hbe (by linarith) (by linarith)
  simp only [zero_add]
  have ha0 : 0 < upBeforeDownExpectation P D.X q ε (b+ε) := by rw [hA0]; exact div_pos h0 hw
  have hb0 : downBeforeUpExpectation P D.X q ε (b+ε) < 1 := by linarith [hm0.2]
  refine ⟨ha0, hb0, hmx.1, ?_⟩
  rw [hAx,hBx,hA0,hB0]
  rw [hB0] at hb0
  exact p2m810_reset_quotient_algebra _ _ _ _ _ _ h0 hw hb0
