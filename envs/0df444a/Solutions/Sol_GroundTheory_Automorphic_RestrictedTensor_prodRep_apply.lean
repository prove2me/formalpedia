-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.prodRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:23:50.524847+00:00
-- url     : https://prove2.me/submissions/b6745b89-2610-4f36-9ae3-e11f8f1a61f7

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
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (ρ₁ : Representation ℂ M₁ V) (ρ₂ : Representation ℂ M₂ V) (hcomm)
    (p : M₁ × M₂) (v : V) : prodRep ρ₁ ρ₂ hcomm p v = ρ₁ p.1 (ρ₂ p.2 v) :=
  rfl
end GroundTheory.Automorphic.RestrictedTensor
