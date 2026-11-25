-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_contractLeft_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:32:44.346303+00:00
-- url     : https://prove2.me/submissions/d3800d5e-2634-4f8a-8d0c-7a3c57c907cd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractRight_tmul
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractLeft_tmul
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_contractRight_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set TensorProduct
open scoped TensorProduct
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
  {V₁ V₂ V₁' V₂' : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₁'] [Module ℂ V₁'] [AddCommGroup V₂'] [Module ℂ V₂']
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {z : V₁ ⊗[ℂ] V₂} (hz : z ≠ 0) :
    ∃ l : Dual ℂ V₁, contractLeft l z ≠ 0 := by
  obtain ⟨l, hl⟩ := exists_contractRight_ne_zero (V₁ := V₂) (V₂ := V₁)
    (z := TensorProduct.comm ℂ V₁ V₂ z) (fun h => hz (by
      have := congrArg (TensorProduct.comm ℂ V₁ V₂).symm h
      simpa using this))
  refine ⟨l, ?_⟩
  have key : ∀ z' : V₁ ⊗[ℂ] V₂,
      contractLeft (V₂ := V₂) l z' = contractRight l (TensorProduct.comm ℂ V₁ V₂ z') := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [contractLeft_tmul, contractRight_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rwa [key]
end GroundTheory.Automorphic.RestrictedTensor
