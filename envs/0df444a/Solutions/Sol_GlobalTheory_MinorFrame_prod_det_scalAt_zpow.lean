-- Prove2me | solution 1 for GlobalTheory.MinorFrame.prod_det_scalAt_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:08:27.038791+00:00
-- url     : https://prove2.me/submissions/bfe023cb-72cf-4581-9d26-b12fbb5ad281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
namespace GlobalTheory.MinorFrame
theorem _root_.solution {ι : Type} [Fintype ι] {a : ℕ} (τ₀ : ι) (ζ : ℂ) (m : ι → ℤ) (n : ℕ)
    (hn : (n : ℤ) = m τ₀) : (∏ τ, (scalAt (a := a) τ₀ ζ τ).det ^ (m τ)) = ζ ^ (a * n) := by
  rw [Finset.prod_eq_single τ₀]
  · simp [scalAt, Matrix.det_smul, ← hn, zpow_natCast, pow_mul]
  · intro τ _ h
    simp [scalAt, h]
  · simp
end GlobalTheory.MinorFrame
