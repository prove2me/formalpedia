-- Prove2me | solution 1 for GlobalTheory.MinorFrame.constantCoeff_rsub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:09:27.480538+00:00
-- url     : https://prove2.me/submissions/1afe9653-9b63-49ca-a57f-47b25262061b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjoint
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_MinorFrame_rsub_X
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
open MvPolynomial Matrix Formalism.L2.DIV
open GlobalTheory GlobalTheory.MinorFrame
variable {σ σ' : Type} [Fintype σ] [Fintype σ']
namespace GlobalTheory.MinorFrame
theorem _root_.solution (M : Matrix σ' σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (rsub M g) = constantCoeff g := by
  have : (constantCoeff : MvPolynomial σ' ℂ →+* ℂ).comp (rsub M).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [rsub_X]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* ℂ => φ g) this
end GlobalTheory.MinorFrame
