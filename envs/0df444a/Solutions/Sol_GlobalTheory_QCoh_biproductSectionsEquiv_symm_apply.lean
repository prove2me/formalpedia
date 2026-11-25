-- Prove2me | solution 1 for GlobalTheory.QCoh.biproductSectionsEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:06:17.43172+00:00
-- url     : https://prove2.me/submissions/25effef8-1dd7-479c-97d4-226dff25ecf7

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
theorem _root_.solution {ι : Type} [Fintype ι] (F : ι → X.Modules)
    [HasBiproduct F] (U : X.Opens) (s : ∀ i, Γ(F i, U)) :
    (biproductSectionsEquiv F U).symm s = ∑ i, (biproduct.ι F i).app U (s i) := rfl
end GlobalTheory.QCoh
