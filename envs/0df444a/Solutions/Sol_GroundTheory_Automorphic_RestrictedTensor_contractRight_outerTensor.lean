-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.contractRight_outerTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:25:10.772469+00:00
-- url     : https://prove2.me/submissions/94397678-9c89-4ab6-b791-f8cfa1b2ef4d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractRight_tmul
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_outerTensor_tmul


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
theorem _root_.solution (π₁ : Representation ℂ M₁ V₁) (π₂ : Representation ℂ M₂ V₂)
    (l : Dual ℂ V₂) (a : M₁) (z : V₁ ⊗[ℂ] V₂) :
    contractRight l (outerTensor π₁ π₂ (a, 1) z) = π₁ a (contractRight l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [outerTensor_tmul, contractRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
end GroundTheory.Automorphic.RestrictedTensor
