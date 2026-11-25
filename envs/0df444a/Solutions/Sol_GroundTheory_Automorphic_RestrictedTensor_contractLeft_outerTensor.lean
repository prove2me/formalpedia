-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.contractLeft_outerTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:10.69278+00:00
-- url     : https://prove2.me/submissions/a6837285-cbdf-4bc4-8b28-a2681f195dc8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractLeft_tmul
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
    (l : Dual ℂ V₁) (b : M₂) (z : V₁ ⊗[ℂ] V₂) :
    contractLeft l (outerTensor π₁ π₂ (1, b) z) = π₂ b (contractLeft l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [outerTensor_tmul, contractLeft_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
end GroundTheory.Automorphic.RestrictedTensor
