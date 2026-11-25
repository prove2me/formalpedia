-- Prove2me | solution 1 for GlobalTheory.QCoh.appLinear_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:47.255893+00:00
-- url     : https://prove2.me/submissions/b0fc6f06-9c47-44c7-a8a7-a598b0c4972a

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
theorem _root_.solution (M : X.Modules) (U : X.Opens) : appLinear (𝟙 M) U = LinearMap.id := rfl
end GlobalTheory.QCoh
