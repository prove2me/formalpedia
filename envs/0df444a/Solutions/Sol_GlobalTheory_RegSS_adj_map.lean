-- Prove2me | solution 1 for GlobalTheory.RegSS.adj_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:06:19.65642+00:00
-- url     : https://prove2.me/submissions/40eb110a-07da-4a98-8a7c-0c1c8e7be711

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
theorem _root_.solution {B : Type} [CommRing B] (σ : A →+* A) (τ : B →+* B)
    (f : A →+* B) (hf : ∀ x, f (σ x) = τ (f x)) {J : Matrix n n A} (hJ : IsUnit J.det)
    (a : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj τ (J.map f) (a.map f) = (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a).map f := by
  have hcT : _root_.Formalism.UG.cT τ (a.map f) = (_root_.Formalism.UG.cT σ a).map f := by
    ext i j
    simp [_root_.Formalism.UG.cT, hf]
  have hinv : (J.map f)⁻¹ = J⁻¹.map f := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ, Matrix.map_one f f.map_zero f.map_one]
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, hcT, hinv, Matrix.map_mul]
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
