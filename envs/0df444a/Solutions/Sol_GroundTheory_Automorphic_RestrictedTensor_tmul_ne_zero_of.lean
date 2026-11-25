-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.tmul_ne_zero_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:49.899189+00:00
-- url     : https://prove2.me/submissions/9f198b7d-c662-4402-870a-cd7259703f31

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractRight_tmul

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
theorem _root_.solution {x : V₁} {y : V₂} (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨l, hl⟩ : ∃ l : Dual ℂ V₂, l y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hcon)
  intro h
  have := congrArg (contractRight l) h
  rw [contractRight_tmul, map_zero] at this
  exact (smul_ne_zero hl hx) this
end GroundTheory.Automorphic.RestrictedTensor
