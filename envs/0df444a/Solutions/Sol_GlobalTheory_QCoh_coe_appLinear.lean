-- Prove2me | solution 1 for GlobalTheory.QCoh.coe_appLinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:06:19.586669+00:00
-- url     : https://prove2.me/submissions/0f92958d-1d4d-4ef5-a9b2-773673aff49f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution (φ : M ⟶ N) (U : X.Opens) : ⇑(appLinear φ U) = φ.app U := rfl
end GlobalTheory.QCoh
