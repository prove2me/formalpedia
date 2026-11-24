-- Prove2me | solution 1 for GlobalTheory.norm_eisTerm_zero_le_of_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:32.321064+00:00
-- url     : https://prove2.me/submissions/fe71102f-b384-4e60-887b-2ea283f965ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormFderivLeOfClosedBallSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOn
import Theorems.Thm_GlobalTheory_eisTerm_at_zero_eq
import Theorems.Thm_GlobalTheory_norm_latPt_le_two_mul_of_near
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_latPt_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open Metric Complex
open GlobalTheory
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] [NumberField F] {z z₀ : Emb F → ℂ} {r : ℝ}
    (hz₀ : z₀ ∈ upperHalf F) (hr : ∀ τ, 2 * r ≤ (z₀ τ).im) (hz : ‖z - z₀‖ < r) (k : ℕ) {p : F × F} (hp : p ≠ 0) :
    ‖eisTerm k 0 z p‖ ≤ (2 ^ Fintype.card (Emb F)) ^ k * ‖eisTerm k 0 z₀ p‖ := by
  rw [eisTerm_at_zero_eq, eisTerm_at_zero_eq, norm_pow, norm_pow, norm_inv, norm_inv, norm_prod, norm_prod, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  have hA : 0 < ∏ τ, ‖latPt z₀ p τ‖ :=
    Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz₀ hp τ)
  have hAB : ∏ τ, ‖latPt z₀ p τ‖ ≤ 2 ^ Fintype.card (Emb F) * ∏ τ, ‖latPt z p τ‖ := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun τ _ => norm_nonneg _) fun τ _ => norm_latPt_le_two_mul_of_near hr hz p τ
  have h2 : (0 : ℝ) < 2 ^ Fintype.card (Emb F) := by positivity
  have hB : 0 < ∏ τ, ‖latPt z p τ‖ := by
    by_contra h
    push_neg at h
    nlinarith
  rw [inv_le_comm₀ hB (by positivity), mul_inv, inv_inv]
  calc (2 ^ Fintype.card (Emb F))⁻¹ * ∏ τ, ‖latPt z₀ p τ‖ ≤ (2 ^ Fintype.card (Emb F))⁻¹ * (2 ^ Fintype.card (Emb F) * ∏ τ, ‖latPt z p τ‖) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
    _ = ∏ τ, ‖latPt z p τ‖ := by field_simp
end GlobalTheory
