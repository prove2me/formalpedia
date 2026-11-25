-- Prove2me | solution 1 for GlobalTheory.QCoh.biprodSectionsEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:11:11.976309+00:00
-- url     : https://prove2.me/submissions/724dc1cc-9491-4c7d-b658-277a765bdd81

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
theorem _root_.solution (M N : X.Modules) (U : X.Opens) (s : Γ(M ⊞ N, U)) :
    biprodSectionsEquiv M N U s =
      ((biprod.fst : M ⊞ N ⟶ M).app U s, (biprod.snd : M ⊞ N ⟶ N).app U s) := rfl
end GlobalTheory.QCoh
