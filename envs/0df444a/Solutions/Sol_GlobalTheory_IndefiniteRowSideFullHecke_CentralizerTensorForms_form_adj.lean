-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:49:50.021988+00:00
-- url     : https://prove2.me/submissions/2d192886-32f7-4099-bba9-c3a620b59ed5

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CentralizerTensorForms_hform_eq
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
open Matrix Formalism.UG NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
open Matrix NumberField
open scoped TensorProduct
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
theorem _root_.solution (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (l : Matrix n n A) (y y' : n → A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form σ J y (l *ᵥ y') =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form σ J (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J l *ᵥ y) y' := by
  have hJJ : J * _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J l = _root_.Formalism.UG.cT σ l * J := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul]
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form, _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq]
  rw [mulVec_mulVec, hJJ, ← mulVec_mulVec, dotProduct_mulVec (fun i => σ (y' i))]
  congr 1
  funext i
  unfold _root_.Formalism.UG.cT
  simp [vecMul, mulVec, dotProduct, map_sum, mul_comm]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
end GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
