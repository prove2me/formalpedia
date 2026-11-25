-- Prove2me | solution 1 for GlobalTheory.UnifConsts.submatrix_blockEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:00:23.827835+00:00
-- url     : https://prove2.me/submissions/5ff67e5b-ca39-4401-bc48-891a92e29ff2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydisc
import Theorems.Thm_GlobalTheory_UnifConsts_blockEquiv_inr
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
open GlobalTheory GlobalTheory.UnifConsts
namespace GlobalTheory.UnifConsts
theorem _root_.solution {g rk : ℕ} (Y S : Matrix (Fin g) (Fin g) ℝ) (T : ℝ)
    (hY : ∀ j k, Y j k = Y k j) (hS : ∀ j k, (rk ≤ j.val ∨ rk ≤ k.val) → S j k = 0) :
    (Y + T • S).submatrix (blockEquiv g rk) (blockEquiv g rk) =
      fromBlocks
        (Y.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inl) +
          T • S.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inl))
        (Y.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inr))
        (Y.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inr))ᵀ
        (Y.submatrix (blockEquiv g rk ∘ Sum.inr) (blockEquiv g rk ∘ Sum.inr)) := by
  ext (i | i) (j | j)
  · simp
  · simp [hS _ _ (Or.inr (not_lt.1 (blockEquiv_inr g rk j)))]
  · simp [hS _ _ (Or.inl (not_lt.1 (blockEquiv_inr g rk i))), hY]
  · simp [hS _ _ (Or.inl (not_lt.1 (blockEquiv_inr g rk i)))]
end GlobalTheory.UnifConsts
