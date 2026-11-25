-- Prove2me | solution 1 for GlobalTheory.QCoh.hom_app_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:00.454896+00:00
-- url     : https://prove2.me/submissions/fb6369ac-a7ce-4a1c-a177-071628ab6646

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X Y : Scheme.{u}}
namespace GlobalTheory.QCoh
theorem _root_.solution {F F' : X.Modules} (φ : F ⟶ F') {U V : X.Opens} (h : V ≤ U) (s : Γ(F, U)) :
    φ.app V (F.presheaf.map (homOfLE h).op s) = F'.presheaf.map (homOfLE h).op (φ.app U s) :=
  congr($(φ.mapPresheaf.naturality (homOfLE h).op) s)
end GlobalTheory.QCoh
