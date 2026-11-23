-- Prove2me | solution 1 for GlobalTheory.innerFormLeft_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:35.219021+00:00
-- url     : https://prove2.me/submissions/000aa417-9043-4779-991d-2bb279ed964d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution (u v : V) : innerFormLeft V u v = inner ℂ v u := rfl
end GlobalTheory
