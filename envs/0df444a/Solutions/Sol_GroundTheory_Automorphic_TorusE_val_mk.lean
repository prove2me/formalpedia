-- Prove2me | solution 1 for GroundTheory.Automorphic.TorusE.val_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:10:40.726623+00:00
-- url     : https://prove2.me/submissions/7cf3cf49-1477-4bf3-b604-1df437429bf2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus

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
variable {V : Type*} [AddCommGroup V] [Module E V]
variable [FiniteDimensional E V]
open GroundTheory.Automorphic.TorusE
variable {γ : V ≃ₗ[E] V}
omit [FiniteDimensional E V]
namespace GroundTheory.Automorphic.TorusE
theorem _root_.solution (t : V ≃ₗ[E] V) (ht : t ∈ torusE γ) : (mk t ht).val = t := rfl
end GroundTheory.Automorphic.TorusE
