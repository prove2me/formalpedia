-- Prove2me | solution 1 for GlobalTheory.PDivGroup.lTensor_transl_comul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:20.23117+00:00
-- url     : https://prove2.me/submissions/5fb389bd-163a-4010-bb8a-ddfefec2e9be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoboundaryTranslationInvariantPTorsion
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_succ
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_zero
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDivGroup_rigLevel_mk
import Theorems.Thm_GlobalTheory_PDivGroup_transl_apply
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
open GlobalTheory
open GlobalTheory.PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) (x : G.A (n + 1)) :
    (G.transl n).toLinearMap.lTensor (G.A (n + 1)) (comul (R := R) x) =
      TensorProduct.assoc R _ _ _ ((comul (R := R)).rTensor (G.A 1) (G.transl n x)) := by
  have h1 : (G.transl n).toLinearMap =
      (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ ∘ₗ comul :=
    LinearMap.ext fun a => G.transl_apply n a
  have h2 : ∀ t : (G.A (n + 1) ⊗[R] G.A (n + 1)) ⊗[R] G.A (n + 1),
      ((G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _).lTensor _ (TensorProduct.assoc R _ _ _ t) =
        TensorProduct.assoc R _ _ _ ((G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ t) := by
    intro t
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul u c =>
      induction u with
      | zero => simp
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul a b => simp
  rw [h1, LinearMap.lTensor_comp_apply, ← coassoc_apply, h2, transl_apply]
  congr 1
  generalize comul (R := R) x = t
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp
end GlobalTheory.PDivGroup
