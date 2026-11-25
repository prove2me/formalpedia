-- Prove2me | solution 1 for GroundTheory.Automorphic.TorusE.val_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:01:58.928836+00:00
-- url     : https://prove2.me/submissions/ecea15a2-2731-4eb7-96b6-aa63a3cae297

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
variable [Fact (IsRegularSemisimple γ)]
namespace GroundTheory.Automorphic.TorusE
theorem _root_.solution (a : TorusE γ) : a⁻¹.val = a.val⁻¹ := rfl
end GroundTheory.Automorphic.TorusE
