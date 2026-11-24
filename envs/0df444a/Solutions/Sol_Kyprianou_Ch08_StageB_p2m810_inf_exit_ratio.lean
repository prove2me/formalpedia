-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_inf_exit_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:15:51.338967+00:00
-- url     : https://prove2.me/submissions/7271bd20-a581-48b4-9a98-8426eb025673
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_ge_one
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_reset_squeeze
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_reset_sandwich
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_reset_ratio_limit
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      (∫ ω, discountedAt q (reflectedInfExit D.X x a ω) ∂P) =
        Zscale q (W q) x / Zscale q (W q) a := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa
  have h8 := source_result8_2_v2
  unfold sourceCertificate_result8_2 at h8
  obtain ⟨n, hLaw, hRep, _, _⟩ := h8 Ω P D ψ W hψ hW q hq
  have hz : Zscale q (W q) a ≠ 0 := by
    have h := source_zscale_ge_one ψ W hW q a hq ha.le
    linarith
  obtain ⟨h1, h2⟩ := p2m810_inf_reset_ratio_limit ψ W hW q x a hq ha hx hxa hRep.1
  obtain ⟨hF, hs⟩ := p2m810_inf_reset_sandwich Ω P D ψ W hψ hW q x a hq ha hx hxa
  let R := fun (ε b : ℝ) =>
    (Zscale q (W q) (x+ε) - W q (x+ε) *
      ((Zscale q (W q) ε - 1) / W q ε)) /
    (Zscale q (W q) (b+ε) - W q (b+ε) *
      ((Zscale q (W q) ε - 1) / W q ε))
  exact p2m810_inf_reset_squeeze R _ _ x a ha hxa hF
    (fun h => by simp [h, hz]) hs h1 h2
