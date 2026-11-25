-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.stableInv_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:41.093781+00:00
-- url     : https://prove2.me/submissions/ed3e7ef0-5f48-446e-a957-9ab3259adfcb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_invOf_eq_of_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) :
    h.stableInv γ (g * γ * g⁻¹) = h.invOf γ g hg := by
  have H : ∃ g' : V ≃ₗ[E] V, g' * γ * g'⁻¹ = g * γ * g⁻¹ ∧ g * γ * g⁻¹ ∈ h.unitaryGroup :=
    ⟨g, rfl, hg⟩
  rw [stableInv, dif_pos H]
  exact h.invOf_eq_of_eq γ _ _ _ _ H.choose_spec.1
end GroundTheory.Automorphic.HermitianForm
