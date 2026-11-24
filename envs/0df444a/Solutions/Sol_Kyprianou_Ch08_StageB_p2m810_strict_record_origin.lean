-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_strict_record_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:24:17.351444+00:00
-- url     : https://prove2.me/submissions/e27d4f0a-ba44-47ca-b8e9-e4da04e95afa

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_strict_height_discount_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_excursion_strict_tail_limit
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict record transform using the right derivative. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q a l : ℝ), 0 ≤ q → 0 < a → 0 < l →
      (∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X 0 a ω
        then discountedAt q (tauPlus D.X l ω) else 0 ∂P) =
      Real.exp (-(derivWithin (W q) (Ici a) a / W q a) * l) := by
  intro Ω mΩ P hP D ψ W hψ hW q a l hq ha hl
  have h8 := source_result8_2_v2
  unfold sourceCertificate_result8_2 at h8
  obtain ⟨n, hLaw, hRep, hder, _⟩ := h8 Ω P D ψ W hψ hW q hq
  obtain ⟨dl, dr, hdl, hdr, hdl', hdr', heq⟩ := hder a ha
  have ht := p2m810_excursion_strict_tail_limit n a (hLaw.2 l a hl ha).1
  have he := Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := -l)).mul ht)
  have he' := p2m810_strict_height_discount_limit Ω P D ψ W hψ hW q a l hq ha hl
  have heq' := tendsto_nhds_unique he' (he.congr (fun k => by
    exact (hLaw.2 l (a+1/((k:ℝ)+1)) hl (by positivity)).2.symm))
  rw [hdr.derivWithin (uniqueDiffWithinAt_Ici a), hdr',
    mul_div_cancel_right₀ _ (hRep.1 a ha).ne']
  apply (mul_left_cancel₀ (Real.exp_ne_zero (Phi ψ q*l)))
  rw [heq', ← Real.exp_add]
  congr 1
  ring
