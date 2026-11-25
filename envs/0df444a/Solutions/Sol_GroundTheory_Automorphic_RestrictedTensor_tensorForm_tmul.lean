-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.tensorForm_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:23:52.682191+00:00
-- url     : https://prove2.me/submissions/f71a09e1-c6d5-4d6b-8263-c5b5e76c8d42

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor

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
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ρ₁ : Representation ℂ M₁ V} {ρ₂ : Representation ℂ M₂ V}
  {hcomm : ∀ a b, ρ₁ a * ρ₂ b = ρ₂ b * ρ₁ a} {e₁ e₂ : End ℂ V}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] (φ : Dual ℂ V₁) (ψ : Dual ℂ V₂) (x : V₁) (y : V₂) :
    tensorForm φ ψ (x ⊗ₜ y) = φ x * ψ y := by
  simp [tensorForm]
end GroundTheory.Automorphic.RestrictedTensor
