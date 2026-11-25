-- Prove2me | solution 1 for GlobalTheory.QCoh.pullbackSections_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:14.897566+00:00
-- url     : https://prove2.me/submissions/b65940e6-a679-45d9-acec-38649ae40d61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
import Theorems.Thm_GlobalTheory_QCoh_hom_app_res
import Theorems.Thm_GlobalTheory_QCoh_res_res


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
theorem _root_.solution (e : U ≤ f ⁻¹ᵁ V') (h : V' ≤ V) (s : Γ(G, V)) :
    pullbackSections f G e (G.presheaf.map (homOfLE h).op s) =
      pullbackSections f G (e.trans (f.preimage_mono h)) s :=
  (congr(((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE e).op
    $(hom_app_res ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) h s))).trans
    (res_res ((Scheme.Modules.pullback f).obj G) (f.preimage_mono h) e _)
end GlobalTheory.QCoh
