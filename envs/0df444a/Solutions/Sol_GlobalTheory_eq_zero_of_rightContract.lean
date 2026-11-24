-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_rightContract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:11.610162+00:00
-- url     : https://prove2.me/submissions/a3803f4a-5f7f-4c73-99c1-2dec121b73c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EigenTensorFullLeftSupport
import Theorems.Thm_GlobalTheory_rightContract_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TensorProduct
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (w : TensorProduct F E E')
    (h : ∀ l : E' →ₗ[F] F, rightContract l w = 0) : w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F E'
  have key : ∀ (i) (v : TensorProduct F E E'),
      TensorProduct.equivFinsuppOfBasisRight b v i = rightContract (b.coord i) v := by
    intro i v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [rightContract_tmul]
    | add a c ha hc => simp only [map_add, Finsupp.add_apply, ha, hc]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, h]
  simp
end GlobalTheory
