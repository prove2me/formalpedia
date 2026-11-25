-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.normOf_eq_of_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:52.582931+00:00
-- url     : https://prove2.me/submissions/2c9156b7-69c2-48e8-a760-60dbde1abcc0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
import Theorems.Thm_GroundTheory_Automorphic_TorusE_ext


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
theorem _root_.solution (g g' : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup)
    (hg' : g' * γ * g'⁻¹ ∈ h.unitaryGroup)
    (hgg : h.adjointEquiv g * g = h.adjointEquiv g' * g') : h.normOf γ g hg = h.normOf γ g' hg' :=
  Subtype.ext (TorusE.ext hgg)
end GroundTheory.Automorphic.HermitianForm
