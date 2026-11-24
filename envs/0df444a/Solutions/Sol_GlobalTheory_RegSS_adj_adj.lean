-- Prove2me | solution 1 for GlobalTheory.RegSS.adj_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:55:12.285803+00:00
-- url     : https://prove2.me/submissions/6ed62377-1ecb-4485-8bc2-ec50ce54ff5f

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
theorem _root_.solution (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x)
    {J : Matrix n n A} (hH : _root_.Formalism.UG.IsHerm σ J) (hJ : IsUnit J.det) (a : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a) = a := by
  have hc : ∀ M : Matrix n n A, _root_.Formalism.UG.cT σ (_root_.Formalism.UG.cT σ M) = M := by
    intro M
    ext i j
    simp [_root_.Formalism.UG.cT, hσ]
  have hH' : _root_.Formalism.UG.cT σ J = J := hH
  have hJi : _root_.Formalism.UG.cT σ J⁻¹ = J⁻¹ := by
    have hl : _root_.Formalism.UG.cT σ J⁻¹ * J = 1 := by
      calc _root_.Formalism.UG.cT σ J⁻¹ * J = _root_.Formalism.UG.cT σ J⁻¹ * _root_.Formalism.UG.cT σ J := by rw [hH']
        _ = _root_.Formalism.UG.cT σ (J * J⁻¹) := (_root_.Formalism.UG.cT_mul σ J J⁻¹).symm
        _ = 1 := by rw [Matrix.mul_nonsing_inv _ hJ, _root_.Formalism.UG.cT_one]
    exact (Matrix.inv_eq_left_inv hl).symm
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, _root_.Formalism.UG.cT_mul, hc, hJi, hH']
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ,
    Matrix.mul_one]
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
