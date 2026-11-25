-- Prove2me | solution 1 for GlobalTheory.DetInv.psi_phi_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:32.004522+00:00
-- url     : https://prove2.me/submissions/50993dbe-4b6d-44b0-a4e2-c1565ecd232a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusOfPadic
import Theorems.Thm_P2M_GlobalTheory_DetInv_PsiPhi_frobenius_phiInv__7e3fdf573703
import Theorems.Thm_P2M_GlobalTheory_DetInv_PsiPhi_phiInv_frobenius__8a17b581bd6d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
open GlobalTheory GlobalTheory.DetInv
open PsiPhi
namespace GlobalTheory.DetInv
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ],
    (∀ c : ℤ_[p], phiInv p O (ofPadic p O c) = ofPadic p O c) ∧ Function.Bijective (phiInv p O) ∧
    ∃ ψ φ : RL p O Λ →+* RL p O Λ, IsPsi ψ ∧
      (∀ (a : Ainf p O) (l : Λ), φ (a ⊗ₜ l) = WittVector.frobenius a ⊗ₜ l) ∧
      (∀ r, φ (ψ r) = r) ∧ ∀ r, ψ (φ r) = r := by
  intro p _ O _ _ _ Λ _ _
  refine ⟨fun c => phiInv_ofPadic c,
    Function.bijective_iff_has_inverse.mpr ⟨WittVector.frobenius, frobenius_phiInv', phiInv_frobenius'⟩,
    (Algebra.TensorProduct.map (phiInvAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom,
    (Algebra.TensorProduct.map (frobAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom,
    fun a l => rfl, fun a l => rfl, ?_, ?_⟩
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      change (frobAlg (phiInvAlg a)) ⊗ₜ l = a ⊗ₜ l
      exact congrArg (· ⊗ₜ[ℤ_[p]] l) (frobenius_phiInv' a)
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      change (phiInvAlg (frobAlg a)) ⊗ₜ l = a ⊗ₜ l
      exact congrArg (· ⊗ₜ[ℤ_[p]] l) (phiInv_frobenius' a)
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
end GlobalTheory.DetInv
