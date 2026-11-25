-- Prove2me | solution 1 for GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:42:05.750969+00:00
-- url     : https://prove2.me/submissions/b22e55a9-809d-4fd9-b2e9-88bdc14c317e

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionsFlatBaseChangeBijective
import Theorems.Thm_GlobalTheory_PDiv_cobOne_baseChange
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
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
open GlobalTheory GlobalTheory.PDiv
namespace GlobalTheory.PDiv
theorem _root_.solution {R A : Type} (R' : Type) [CommRing R] [CommRing A]
    [Bialgebra R A] [CommRing R'] [Algebra R R'] [Module.Flat R R'] :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  set K := LinearMap.ker (cobOne R A)
  have hsub : ∀ y : R' ⊗[R] K,
      (liftSemi (toBaseChange R R' A).prim y).1 = K.subtype.lTensor R' y := by
    intro y
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
    | tmul r b =>
      rw [liftSemi_tmul, Submodule.coe_smul, SemiBialgHom.prim_val, toBaseChange_apply,
        LinearMap.lTensor_tmul, Submodule.subtype_apply, smul_tmul', smul_eq_mul, mul_one]
  have hex := Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map (cobOne R A))
  refine ⟨fun x y h => ?_, fun z => ?_⟩
  · refine Module.Flat.lTensor_preserves_injective_linearMap (M := R') K.subtype
      K.injective_subtype ?_
    rw [← hsub, ← hsub, h]
  · obtain ⟨x, hx⟩ := z
    have hz : (cobOne R A).lTensor R' x = 0 := by
      have h0 : cobOne R' (R' ⊗[R] A) x = 0 := hx
      rw [cobOne_baseChange, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_eq_zero_iff, LinearMap.baseChange_eq_ltensor] at h0
      exact h0
    obtain ⟨y, hy⟩ := (hex x).1 hz
    exact ⟨y, Subtype.ext ((hsub y).trans hy)⟩
end GlobalTheory.PDiv
