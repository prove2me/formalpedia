-- Prove2me | solution 1 for GlobalTheory.RegSS.sigR_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:15:19.632524+00:00
-- url     : https://prove2.me/submissions/97d8029a-7f46-4f47-8cc8-6d92540b14ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
open Matrix NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (R : Type) [CommRing R]
    [Algebra F R] (x : E ⊗[F] R) : _root_.Formalism.UG.sigR σ R (_root_.Formalism.UG.sigR σ R x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e r => simp [_root_.Formalism.UG.sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
