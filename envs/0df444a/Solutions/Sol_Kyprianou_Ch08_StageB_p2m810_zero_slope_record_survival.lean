-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_zero_slope_record_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:26:46.056269+00:00
-- url     : https://prove2.me/submissions/ac705efe-9310-4ebd-8096-28d3529f4902

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_record_survival_pointwise
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
/-- The strict drawdown record survival law at zero slope. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      derivWithin (W q) (Ici a) a = 0 →
      q = 0 ∧ ∀ l : ℝ, x < l →
        (∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X 0 a ω
          then discountedAt q (tauPlus D.X l ω) else 0 ∂P) = 1 := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa hz
  have h8 := source_result8_2_v2
  unfold sourceCertificate_result8_2 at h8
  obtain ⟨n, hLaw, hRep, hder, _⟩ := h8 Ω P D ψ W hψ hW q hq
  obtain ⟨dl, dr, hl, hr, hdl, hdr, heq⟩ := hder a ha
  have hw := hRep.1 a ha
  rw [hr.derivWithin (uniqueDiffWithinAt_Ici a), hdr] at hz
  have hr0 := ((hW q hq).1.2.1).1
  have hφ : Phi ψ q = 0 := by
    have hsum := (mul_eq_zero.mp hz).resolve_right hw.ne'
    linarith [ENNReal.toReal_nonneg (a := n (Ioi a))]
  have hroot := ((hW q hq).1.2.1).2
  have hψ0 : ψ 0 = 0 := by
    simpa [SpectrallyNegativeModel.toData] using (hψ 0 1 le_rfl zero_lt_one).2
  rw [hφ,hψ0] at hroot
  refine ⟨hroot.symm, ?_⟩
  intro l hl
  have h := p2m810_record_survival_pointwise Ω P D ψ W hψ hW q 0 a hq ha le_rfl ha.le l (lt_of_le_of_lt hx hl)
  have hdz : derivWithin (W q) (Ici a) a = 0 := by
    rw [hr.derivWithin (uniqueDiffWithinAt_Ici a), hdr]
    exact hz
  simpa [hdz, hw.ne'] using h
