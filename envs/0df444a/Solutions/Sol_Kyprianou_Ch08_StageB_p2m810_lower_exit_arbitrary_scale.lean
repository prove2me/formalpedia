-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_lower_exit_arbitrary_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:26:56.115911+00:00
-- url     : https://prove2.me/submissions/1d06d4e5-5b80-4d83-865f-64971ea26826

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_one_sided_passage
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_stopped_downward_split
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
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
      downBeforeUpExpectation P D.X q x a =
        Zscale q (W q) x - Zscale q (W q) a * W q x / W q a := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa
  obtain ⟨hp, hs, hn⟩ := source_result81_one_sided_passage Ω P D ψ hψ W hW
  have hC : ∃ c : ℝ, ∀ z : ℝ,
      downExpectation P D.X q z = Zscale q (W q) z - c * W q z := by
    rcases eq_or_lt_of_le hq with hzero | hpos
    · subst q
      by_cases he : ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d
      · obtain ⟨d, hd⟩ := he
        exact ⟨d, fun z => by simpa [Zscale] using hs z d hd⟩
      · exact ⟨0, fun z => by simpa [Zscale] using hn he z⟩
    · exact ⟨q / Phi ψ q, fun z => hp q z hpos⟩
  obtain ⟨c, hc⟩ := hC
  have h8 := source_result8_2_v2
  unfold sourceCertificate_result8_2 at h8
  obtain ⟨n, hLaw, hRep, _, _⟩ := h8 Ω P D ψ W hψ hW q hq
  have hWa := hRep.1 a ha
  have hu := source_result81_upper_exit_ratio Ω P D ψ hψ W hW q x a hq ha hxa
  have hsplit := source_result81_stopped_downward_split Ω P D q x a hq ha hxa
  rw [hc x, hc a, hu] at hsplit
  have hcancel := div_mul_cancel₀ (W q x) hWa.ne'
  calc
    _ = (Zscale q (W q) x - c * W q x) -
        W q x / W q a * (Zscale q (W q) a - c * W q a) := by linarith only [hsplit]
    _ = Zscale q (W q) x - Zscale q (W q) a * W q x / W q a +
        c * (W q x / W q a * W q a - W q x) := by ring
    _ = _ := by rw [hcancel, sub_self, mul_zero, add_zero]
