-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CellSumProof.cellSum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:38:14.789801+00:00
-- url     : https://prove2.me/submissions/4f7f339e-93e5-4ee0-89c2-d99d6cef86f1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CellSumOfCntBasic
import Theorems.Thm_GlobalTheory_CompanionTheory_CellSumProof_measurable_hits
import Theorems.Thm_GlobalTheory_CompanionTheory_CellSumProof_lintegral_hits
import Theorems.Thm_GlobalTheory_CompanionTheory_CellSumProof_cnt_le_hits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CellSumProof
namespace GlobalTheory.CompanionTheory.CellSumProof
theorem _root_.solution : CellSum := by
  intro X ι _ a Ω₀ Ω w c h₀ hΩ hcov hw hc
  have hcomp : IsCompact (Ω₀ * Ω) := h₀.mul hΩ
  have hmeas : ∀ i, MeasurableSet (a i • (Ω₀ * Ω)) := fun i =>
    (hcomp.smul (a i)).measurableSet
  have hpt : ∀ x, w x * cnt X.Γ Ω x ≤ ∑' i, c i * hits X (a i • (Ω₀ * Ω)) x := by
    intro x
    obtain ⟨δ, hδ, i, o, ho, hx⟩ := hcov x
    have hwx : w x ≤ c i := by
      rw [← hw δ hδ x, hx]
      exact hc i o ho
    calc w x * cnt X.Γ Ω x ≤ c i * hits X (a i • (Ω₀ * Ω)) x :=
          mul_le_mul' hwx (cnt_le_hits X hδ ho hx)
      _ ≤ _ := ENNReal.le_tsum i
  calc ∫⁻ x, w x * cnt X.Γ Ω x ∂X.ν
      ≤ ∫⁻ x, ∑' i, c i * hits X (a i • (Ω₀ * Ω)) x ∂X.ν := lintegral_mono hpt
    _ = ∑' i, ∫⁻ x, c i * hits X (a i • (Ω₀ * Ω)) x ∂X.ν :=
        lintegral_tsum fun i => ((measurable_hits X (hmeas i)).const_mul _).aemeasurable
    _ = ∑' i, c i * X.μ (Ω₀ * Ω) := by
        refine tsum_congr fun i => ?_
        rw [lintegral_const_mul _ (measurable_hits X (hmeas i)), lintegral_hits X (hmeas i),
          measure_smul]
    _ = X.μ (Ω₀ * Ω) * ∑' i, c i := by
        rw [ENNReal.tsum_mul_right, mul_comm]
end GlobalTheory.CompanionTheory.CellSumProof
