-- Prove2me | solution 1 for GlobalTheory.RegSS.mem_UJ_iff_mul_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:36.663752+00:00
-- url     : https://prove2.me/submissions/5f03c5e3-15fa-442b-be70-b4b831b1020d

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
theorem _root_.solution (σ : A →+* A) {J : Matrix n n A}
    (hJ : IsUnit J.det) (g : GL n A) :
    g ∈ _root_.Formalism.UG.UJ σ J ↔ (g : Matrix n n A) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (g : Matrix n n A) = 1 := by
  change _root_.Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J ↔ _
  rw [mul_eq_one_comm]
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj]
  constructor
  · intro hg
    rw [show J⁻¹ * _root_.Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) =
        J⁻¹ * (_root_.Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) by
      simp only [Matrix.mul_assoc], hg, Matrix.nonsing_inv_mul _ hJ]
  · intro hg
    calc _root_.Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)
        = J * (J⁻¹ * _root_.Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.mul_nonsing_inv_cancel_left _ _ hJ]
      _ = J := by rw [hg, Matrix.mul_one]
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
