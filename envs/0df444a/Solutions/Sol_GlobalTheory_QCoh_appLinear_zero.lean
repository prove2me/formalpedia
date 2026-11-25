-- Prove2me | solution 1 for GlobalTheory.QCoh.appLinear_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:49.839316+00:00
-- url     : https://prove2.me/submissions/5e5df6f7-e0a6-4cc8-b353-a04fc9e64fa8

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
theorem _root_.solution (M N : X.Modules) (U : X.Opens) : appLinear (0 : M ⟶ N) U = 0 := rfl
end GlobalTheory.QCoh
