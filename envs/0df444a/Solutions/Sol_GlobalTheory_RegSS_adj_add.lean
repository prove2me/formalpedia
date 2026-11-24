-- Prove2me | solution 1 for GlobalTheory.RegSS.adj_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:14:02.089233+00:00
-- url     : https://prove2.me/submissions/215c47b1-2cb8-4884-ba3d-4bc35afde6b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_GlobalTheory_RegSS_cT_add
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
open Matrix NumberField
open scoped TensorProduct
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution (σ : A →+* A) (J a b : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (a + b) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a + _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J b := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, _root_.GlobalTheory.RegSS.cT_add, Matrix.mul_add, Matrix.add_mul]
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
