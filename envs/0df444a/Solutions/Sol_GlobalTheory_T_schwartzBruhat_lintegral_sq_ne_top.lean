-- Prove2me | solution 1 for GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:41.534219+00:00
-- url     : https://prove2.me/submissions/18efb04e-0772-4e24-b532-b341bce79802

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatLintegralSqNeTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatLintegralSqNeTopStatement
import Theorems.Thm_GlobalTheory_SBNorm_schwartzBruhat_memL2_inner_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : @Measure (Fin n × Fin d → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k),
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ ∧
      ∫ y, f y * (starRingEnd ℂ) (f y) ∂μ = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧
      (f ≠ 0 → ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0) ∧
      ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  first | exact @GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self | exact GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self | (intros; apply GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self <;> assumption)
end _root_.GlobalTheory.T
