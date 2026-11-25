-- Prove2me | solution 1 for GlobalTheory.TranslFree.coassoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:53.628874+00:00
-- url     : https://prove2.me/submissions/7f7966fe-8a3c-4a2d-ac0a-5cdc6eef9fff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslCoactionFreeCoassocCounital
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_IsBicharacter_map
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
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory GlobalTheory.TranslFree
variable {R A B : Type} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B] [Bialgebra R B]
  (f : A →ₐc[R] B)
namespace GlobalTheory.TranslFree
theorem _root_.solution (a : A) :
    TensorProduct.assoc R A B B (((f : A →ₗ[R] B).lTensor A ∘ₗ comul).rTensor B
      ((f : A →ₗ[R] B).lTensor A (comul a))) =
      (comul (R := R) (A := B)).lTensor A ((f : A →ₗ[R] B).lTensor A (comul a)) := by
  let F : A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] (B ⊗[R] B) :=
    (TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B)).lTensor A
  have h1 : ∀ w : A ⊗[R] A,
      TensorProduct.assoc R A B B (((f : A →ₗ[R] B).lTensor A ∘ₗ comul).rTensor B
        ((f : A →ₗ[R] B).lTensor A w)) =
      F (TensorProduct.assoc R A A A ((comul (R := R)).rTensor A w)) := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply]
      generalize comul (R := R) a = w
      induction w with
      | zero => simp
      | add u v hu hv => simp only [map_add, add_tmul, hu, hv]
      | tmul u v => simp [F]
  have h2 : ∀ w : A ⊗[R] A,
      (comul (R := R) (A := B)).lTensor A ((f : A →ₗ[R] B).lTensor A w) =
      F ((comul (R := R)).lTensor A w) := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, F]
      congr 1
      exact (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) b).symm
  rw [h1, h2, Coalgebra.coassoc_apply]
end GlobalTheory.TranslFree
