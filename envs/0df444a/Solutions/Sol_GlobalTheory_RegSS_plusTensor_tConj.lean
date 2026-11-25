-- Prove2me | solution 1 for GlobalTheory.RegSS.plusTensor_tConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:09:04.175623+00:00
-- url     : https://prove2.me/submissions/d42f37dc-68bb-497d-82c5-ea3056eb4555

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_GlobalTheory_RegSS_adj_add
import Theorems.Thm_GlobalTheory_RegSS_adj_zero
import Theorems.Thm_GlobalTheory_RegSS_adj_mul
import Theorems.Thm_GlobalTheory_RegSS_adj_algebraMap
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
variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}
open Matrix NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular σ J γ)
    (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix n n E) ⊗[F] E) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusTensor σ J (γ : Matrix n n E)
        (_root_.GlobalTheory.RegSS.tConj _ σ x) : Matrix n n E) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J
        (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusTensor σ J (γ : Matrix n n E) x : Matrix n n E) := by
  have hJ := h.nondeg
  induction x using TensorProduct.induction_on with
  | zero => simp [_root_.GlobalTheory.RegSS.adj_zero]
  | tmul p e =>
    have hp : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J
        (((p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E))) : Matrix n n E) =
        ((p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) : Matrix n n E) := by
      have hp0 : _root_.Formalism.UG.cT (σ : E →+* E)
          (((p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E))) : Matrix n n E) * J =
          J * ((p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) : Matrix n n E) := p.2
      simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj]
      rw [Matrix.mul_assoc, hp0, Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
    simp only [_root_.GlobalTheory.RegSS.tConj, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusTensor, Algebra.TensorProduct.productMap_apply_tmul,
      Subalgebra.coe_val, IsScalarTower.coe_toAlgHom', MulMemClass.coe_mul,
      Subalgebra.coe_algebraMap]
    rw [_root_.GlobalTheory.RegSS.adj_mul _ hJ, _root_.GlobalTheory.RegSS.adj_algebraMap _ hJ, hp,
      Algebra.commutes]
    rfl
  | add x y hx hy =>
    simp only [map_add, AddMemClass.coe_add, _root_.GlobalTheory.RegSS.adj_add, hx, hy]
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
