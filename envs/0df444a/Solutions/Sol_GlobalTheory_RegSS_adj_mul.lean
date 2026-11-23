-- Prove2me | solution 1 for GlobalTheory.RegSS.adj_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:55.811967+00:00
-- url     : https://prove2.me/submissions/a992a56d-94bf-4d65-ab91-e3c8f8a6503b

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
open Matrix NumberField
open scoped TensorProduct
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (a b : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (a * b) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J b * _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, _root_.Formalism.UG.cT_mul]
  rw [show J⁻¹ * _root_.Formalism.UG.cT σ b * J * (J⁻¹ * _root_.Formalism.UG.cT σ a * J) =
      J⁻¹ * _root_.Formalism.UG.cT σ b * (J * J⁻¹) * _root_.Formalism.UG.cT σ a * J by simp only [Matrix.mul_assoc],
    Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one]
  simp only [Matrix.mul_assoc]
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
