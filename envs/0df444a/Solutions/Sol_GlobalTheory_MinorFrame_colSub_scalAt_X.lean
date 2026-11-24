-- Prove2me | solution 1 for GlobalTheory.MinorFrame.colSub_scalAt_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:49.226179+00:00
-- url     : https://prove2.me/submissions/9263ffeb-e064-4955-874d-143601504269

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
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame
theorem _root_.solution {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (y : Var ι d a) :
    (∑ j' : Fin a, C (scalAt τ₀ ζ y.1 j' y.2.2) * (X (y.1, y.2.1, j') : Pol ι d a)) =
      C (if y.1 = τ₀ then ζ else 1) * X y := by
  obtain ⟨τ, i, j⟩ := y
  by_cases h : τ = τ₀
  · subst h
    rw [Finset.sum_eq_single j]
    · simp [scalAt, Matrix.smul_apply, Matrix.one_apply]
    · intro b _ hb
      simp [scalAt, Matrix.smul_apply, Matrix.one_apply, hb]
    · simp
  · simp [scalAt, h, Matrix.one_apply]
end GlobalTheory.MinorFrame
