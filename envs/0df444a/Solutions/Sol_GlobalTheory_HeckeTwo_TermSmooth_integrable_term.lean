-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermSmooth.integrable_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:26:00.017081+00:00
-- url     : https://prove2.me/submissions/e3fbbe2b-0dcb-4ff9-99bd-e99e8c2975e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_continuous_term
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_norm_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth
namespace GlobalTheory.HeckeTwo.TermSmooth
theorem _root_.solution (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) {a b : ℕ} (m : ℕ) (hab : 2 ≤ a + 2 * b) {y : ℝ}
    (hy : y ≠ 0) : MeasureTheory.Integrable (term σ ν a b m y) := by
  obtain ⟨bd, hbd, h⟩ := norm_term_le σ hσ ν a b m hab hy
  exact hbd.mono' (continuous_term σ ν a b m hy).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t => h t y (Metric.mem_ball_self (by positivity)))
end GlobalTheory.HeckeTwo.TermSmooth
