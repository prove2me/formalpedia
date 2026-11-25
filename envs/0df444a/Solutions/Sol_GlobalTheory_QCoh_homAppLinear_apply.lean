-- Prove2me | solution 1 for GlobalTheory.QCoh.homAppLinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:15.720041+00:00
-- url     : https://prove2.me/submissions/6dea13dc-309e-4ea3-9f42-54d1cfbdc036

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
theorem _root_.solution {F F' : X.Modules} (φ : F ⟶ F') (U : X.Opens) (s : Γ(F, U)) :
    homAppLinear φ U s = φ.app U s := rfl
end GlobalTheory.QCoh
