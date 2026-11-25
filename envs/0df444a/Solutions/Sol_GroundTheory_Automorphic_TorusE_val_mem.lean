-- Prove2me | solution 1 for GroundTheory.Automorphic.TorusE.val_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:01:56.635652+00:00
-- url     : https://prove2.me/submissions/b90dec06-5ebd-46c0-9582-c0f91b8e3310

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
theorem _root_.solution (t : TorusE γ) : t.val ∈ torusE γ := Subtype.prop (p := (· ∈ torusE γ)) t
end GroundTheory.Automorphic.TorusE
