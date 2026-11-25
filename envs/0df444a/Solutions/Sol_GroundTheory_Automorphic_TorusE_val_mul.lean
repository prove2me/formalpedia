-- Prove2me | solution 1 for GroundTheory.Automorphic.TorusE.val_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:01:41.474806+00:00
-- url     : https://prove2.me/submissions/a405e8aa-5c43-44b5-9454-98040508f7c6

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
theorem _root_.solution (a b : TorusE γ) : (a * b).val = a.val * b.val := rfl
end GroundTheory.Automorphic.TorusE
