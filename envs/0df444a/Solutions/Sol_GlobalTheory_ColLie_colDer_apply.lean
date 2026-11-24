-- Prove2me | solution 1 for GlobalTheory.ColLie.colDer_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:21:12.782833+00:00
-- url     : https://prove2.me/submissions/60e926eb-0a38-4f2f-b353-571453b78ad3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
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
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ColLie
open GlobalTheory.MinorFrame
variable {ι : Type} [DecidableEq ι]
namespace GlobalTheory.ColLie
theorem _root_.solution {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colDer τ S P = ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a, S k j • (X (τ, i, k) * pderiv (τ, i, j) P) := by
  simp [colDer, LinearMap.sum_apply]
end GlobalTheory.ColLie
