-- Prove2me | solution 1 for GlobalTheory.QCoh.pullbackSections_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:08.757192+00:00
-- url     : https://prove2.me/submissions/6adfc780-fb78-49b3-9c86-f3ac25a4e9ef

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
variable (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) {U U' : X.Opens} {V V' : Y.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution (e : U ≤ f ⁻¹ᵁ V) (s : Γ(G, V)) :
    pullbackSections f G e s = ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE e).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s) := rfl
end GlobalTheory.QCoh
