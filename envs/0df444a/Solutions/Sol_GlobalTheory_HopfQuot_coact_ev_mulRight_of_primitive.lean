-- Prove2me | solution 1 for GlobalTheory.HopfQuot.coact_ev_mulRight_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:40:42.453805+00:00
-- url     : https://prove2.me/submissions/802951ac-a70a-4868-8306-5f02823b89d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoactionEqAddOfPrimitive
import Theorems.Thm_GlobalTheory_HopfQuot_ev_mulRight_comul_of_primitive
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_succ
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_zero
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDivGroup_rigLevel_mk
import Theorems.Thm_GlobalTheory_PDiv_SemiBialgHom_levelRig_mk
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul
attribute [local simp] GlobalTheory.PDiv.SemiBialgHom.levelRig_mk
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT
attribute [local simp] GlobalTheory.PDivGroup.resOne_succ
attribute [local simp] GlobalTheory.PDivGroup.resOne_zero
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_id
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_mk
attribute [local simp] GlobalTheory.PDivGroup.rigLevel_mk



set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory GlobalTheory.HopfQuot
variable {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
namespace GlobalTheory.HopfQuot
theorem _root_.solution (ρ : B →ₐ[R] B ⊗[R] Λ)
    (hassoc : ∀ a, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ a)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ a))
    (l : Λ →ₗ[R] R) (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : Λ)
    (hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) (f : B) :
    ρ (ev B (l ∘ₗ LinearMap.mulRight R b) (ρ f)) =
      ev B (l ∘ₗ LinearMap.mulRight R b) (ρ f) ⊗ₜ[R] 1 - ev B l (ρ f) ⊗ₜ[R] b := by
  set l' := l ∘ₗ LinearMap.mulRight R b with hl'
  let F : B ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] B ⊗[R] Λ := ((ev Λ l').restrictScalars R).lTensor B
  have h1 : ∀ w : B ⊗[R] Λ, ρ (ev B l' w) =
      F (TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ w)) := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      rw [ev_tmul, map_smul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      generalize ρ a = w
      induction w with
      | zero => simp
      | add u v hu hv => simp only [map_add, smul_add, add_tmul, hu, hv]
      | tmul u v => simp [F]
  have h2 : ∀ w : B ⊗[R] Λ, F ((Coalgebra.comul (R := R)).lTensor B w) =
      ev B l' w ⊗ₜ 1 - ev B l w ⊗ₜ b := by
    intro w
    induction w with
    | zero => simp
    | add a c ha hc =>
      simp only [map_add, add_tmul, ha, hc]
      abel
    | tmul a c =>
      have := ev_mulRight_comul_of_primitive l hl b hb c
      rw [← hl'] at this
      simp only [F, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, this, ev_tmul,
        tmul_sub, smul_tmul]
      rfl
  rw [h1, hassoc, h2]
end GlobalTheory.HopfQuot
