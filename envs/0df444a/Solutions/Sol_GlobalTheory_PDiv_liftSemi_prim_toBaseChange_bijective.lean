-- Prove2me | solution 1 for GlobalTheory.PDiv.liftSemi_prim_toBaseChange_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:14.633534+00:00
-- url     : https://prove2.me/submissions/3962fe5d-577c-4564-9107-65b970978f5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijective
import Theorems.Thm_GlobalTheory_PDiv_cotBaseChange_d
import Theorems.Thm_GlobalTheory_PDiv_cotBaseChange_hom_ext
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_succ
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_zero
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDivGroup_rigLevel_mk
import Theorems.Thm_GlobalTheory_PDiv_SemiBialgHom_levelRig_mk
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_GlobalTheory_T_additiveFunctionCartierDualTangent_bijective
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
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.PDiv
namespace GlobalTheory.PDiv
theorem _root_.solution {R A : Type} (R' : Type) [CommRing R] [CommRing A]
    [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] [CommRing R']
    [Algebra R R'] (hC : Module.Projective R (Cot R (CartierDual R A))) :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  let u := (CartierDual.toDual R (Cot R (CartierDual R A))).symm.toLinearMap ∘ₗ primTangent R A
  have hu : Function.Bijective u :=
    (CartierDual.toDual R _).symm.bijective.comp (GlobalTheory.T.additiveFunctionCartierDualTangent_bijective (R := R) (A := A))
  have key : ⇑(primTangent R' (R' ⊗[R] A)) ∘ ⇑(liftSemi (toBaseChange R R' A).prim) =
      ⇑(CartierDual.toDual R' _) ∘
        ⇑(CartierDual.transpose (cotBaseChange (R := R) (A := A) R').toLinearMap) ∘
        ⇑(CartierDual.baseChangeLinear R R' (Cot R (CartierDual R A))) ∘
        ⇑(LinearMap.lTensor R' u) := by
    funext x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul r b =>
      refine cotBaseChange_hom_ext R' fun φ => ?_
      have h1 : primTangent R' (R' ⊗[R] A) (liftSemi (toBaseChange R R' A).prim (r ⊗ₜ b))
          (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) = φ b.1 • r := by
        rw [liftSemi_tmul, map_smul, LinearMap.smul_apply, primTangent_d, SemiBialgHom.prim_val,
          toBaseChange_apply, CartierDual.baseChange_tmul_tmul, smul_comm, mul_one, smul_eq_mul,
          mul_one]
      refine h1.trans (Eq.symm ?_)
      change CartierDual.baseChangeLinear R R' (Cot R (CartierDual R A)) (r ⊗ₜ u b)
        (cotBaseChange R' (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ)))) = _
      rw [cotBaseChange_d, CartierDual.baseChangeLinear_tmul_tmul, mul_one]
      exact congrArg (· • r) (primTangent_d b φ)
  refine (Function.Bijective.of_comp_iff' (GlobalTheory.T.additiveFunctionCartierDualTangent_bijective (R := R') (A := R' ⊗[R] A)) _).1 ?_
  rw [key]
  exact (CartierDual.toDual R' _).bijective.comp <|
    (CartierDual.transpose_bijective (cotBaseChange R').bijective).comp <|
    (CartierDual.baseChangeLinear_bijective R').comp
      (LinearEquiv.lTensor R' (LinearEquiv.ofBijective u hu)).bijective
end GlobalTheory.PDiv
