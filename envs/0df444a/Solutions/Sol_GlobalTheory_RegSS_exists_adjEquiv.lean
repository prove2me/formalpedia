-- Prove2me | solution 1 for GlobalTheory.RegSS.exists_adjEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:08:47.303556+00:00
-- url     : https://prove2.me/submissions/c893f3d4-7bb2-41bb-96fd-df2b63c5ea71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_GlobalTheory_RegSS_adj_add
import Theorems.Thm_GlobalTheory_RegSS_adj_zero
import Theorems.Thm_GlobalTheory_RegSS_adj_one
import Theorems.Thm_GlobalTheory_RegSS_adj_mul
import Theorems.Thm_GlobalTheory_RegSS_adj_adj
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
    (hA : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ) :
    ∃ τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) ≃ₐ[F]
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E),
      (∀ l, (τ l : Matrix n n E) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J (l : Matrix n n E)) ∧
      (∀ l, τ (τ l) = l) ∧
      (∀ e : E, τ (algebraMap E _ e) = algebraMap E _ (σ e)) ∧
      ∀ l, l ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix n n E) ↔ τ l = l := by
  have hJ := h.nondeg
  have hH := h.herm
  have hσ := h.quad.invol
  have hpres := hA.2.2.2.2.1
  let f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) →
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) :=
    fun l => ⟨_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J l, hpres l l.2⟩
  have hf : ∀ l, (f l : Matrix n n E) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J l := fun _ => rfl
  let τ0 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) →ₐ[F]
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) :=
    { toFun := f
      map_one' := Subtype.ext (by rw [hf]; exact _root_.GlobalTheory.RegSS.adj_one _ hJ)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hc := congrArg Subtype.val (mul_comm (f b) (f a))
        simp only [MulMemClass.coe_mul, hf] at hc ⊢
        rw [_root_.GlobalTheory.RegSS.adj_mul _ hJ, hc]
      map_zero' := Subtype.ext (by rw [hf]; exact _root_.GlobalTheory.RegSS.adj_zero _ _)
      map_add' := fun a b => Subtype.ext (by
        simp only [AddMemClass.coe_add, hf]
        exact _root_.GlobalTheory.RegSS.adj_add _ _ _ _)
      commutes' := fun c => by
        apply Subtype.ext
        rw [hf, IsScalarTower.algebraMap_apply F E (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) c]
        simp only [Subalgebra.coe_algebraMap]
        rw [_root_.GlobalTheory.RegSS.adj_algebraMap _ hJ]
        simp }
  have hτ0 : ∀ l, τ0 (τ0 l) = l := fun l =>
    Subtype.ext (_root_.GlobalTheory.RegSS.adj_adj _ (fun x => hσ x) hH hJ l)
  refine ⟨AlgEquiv.ofAlgHom τ0 τ0 (AlgHom.ext hτ0) (AlgHom.ext hτ0), fun l => rfl, hτ0, ?_, ?_⟩
  · intro e
    apply Subtype.ext
    show _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J
        ((algebraMap E (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) e : Matrix n n E)) = _
    simp only [Subalgebra.coe_algebraMap]
    exact _root_.GlobalTheory.RegSS.adj_algebraMap _ hJ e
  · intro l
    rw [Subtype.ext_iff]
    change _root_.Formalism.UG.cT (σ : E →+* E) (l : Matrix n n E) * J = J * l ↔
      J⁻¹ * _root_.Formalism.UG.cT (σ : E →+* E) (l : Matrix n n E) * J = l
    constructor
    · intro hl
      rw [Matrix.mul_assoc, hl, Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
    · intro hl
      calc _root_.Formalism.UG.cT (σ : E →+* E) (l : Matrix n n E) * J
          = J * (J⁻¹ * _root_.Formalism.UG.cT (σ : E →+* E) (l : Matrix n n E) * J) := by
            rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ]
        _ = J * l := by rw [hl]
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
