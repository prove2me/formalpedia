-- Prove2me | solution 1 for GlobalTheory.oneZ_tmul_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:22.19587+00:00
-- url     : https://prove2.me/submissions/a546f595-acd6-4150-a89d-ffcd2807e9eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : ℕ) (M : ModuleCat.{0} ℤ) (x : M) :
    oneZ p ⊗ₜ[ℤ] ((p : ℤ) • x) = 0 := by
  have h1 := map_zsmul (AddMonoidHom.mk' (fun y : M => oneZ p ⊗ₜ[ℤ] y) (TensorProduct.tmul_add _)) (p : ℤ) x
  have h2 := map_zsmul (AddMonoidHom.mk' (fun b : zmodOverInt p => b ⊗ₜ[ℤ] x)
      (fun b c => TensorProduct.add_tmul b c x)) (p : ℤ) (oneZ p)
  refine (h1.trans h2.symm).trans ((congrArg (fun b => b ⊗ₜ[ℤ] x) ?_).trans (TensorProduct.zero_tmul _ _))
  show ((p : ℤ) • (1 : ZMod p) : ZMod p) = 0
  simp
end GlobalTheory
