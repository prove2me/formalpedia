-- Prove2me | solution 1 for GlobalTheory.QCoh.tildePullbackIso_hom_app_toOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:31.277436+00:00
-- url     : https://prove2.me/submissions/22494fb7-221b-4c58-a4f2-a1f3466ab52e

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
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
theorem _root_.solution (M : ModuleCat.{u} R) (m : M) :
    ((tildePullbackIso φ).hom.app M).app ⊤
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M m)) =
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤
      (tilde.toOpen M ⊤ m) := by
  have := Adjunction.unit_leftAdjointUniq_hom_app
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).ofNatIsoRight
    (pushforwardSpecΓIso φ))
    (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))) M
  exact congr($this m)
end GlobalTheory.QCoh
