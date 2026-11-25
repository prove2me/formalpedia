-- Prove2me | solution 1 for GlobalTheory.RegSS.cT_cT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:06:22.321579+00:00
-- url     : https://prove2.me/submissions/35db333b-b23f-47f0-80ef-5d955c96b776

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
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS
theorem _root_.solution (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (a : Matrix n n A) : cT σ (cT σ a) = a := by
  ext i j; simp [cT, hσ]
end GlobalTheory.RegSS
