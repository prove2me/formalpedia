-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.outerTensor_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:26.427275+00:00
-- url     : https://prove2.me/submissions/d26fddb6-1321-417a-90bf-cc93db69a151

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor

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
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (ρ₁ : Representation ℂ M₁ V₁) (ρ₂ : Representation ℂ M₂ V₂)
    (p : M₁ × M₂) (a : V₁) (b : V₂) :
    outerTensor ρ₁ ρ₂ p (a ⊗ₜ b) = ρ₁ p.1 a ⊗ₜ ρ₂ p.2 b :=
  TensorProduct.map_tmul _ _ _ _
end GroundTheory.Automorphic.RestrictedTensor
