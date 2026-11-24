-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:38:31.405839+00:00
-- url     : https://prove2.me/submissions/66e0eab4-6f1e-4d2f-8c42-38461d39ca9b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
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
theorem _root_.solution (σ : A →+* A) (J : Matrix n n A) (x y : n → A) :
    _root_.Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold _root_.Formalism.UG.hform
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
end GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
