-- Prove2me | solution 1 for GlobalTheory.QCoh.pullback_map_app_pullbackSections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:20:05.227811+00:00
-- url     : https://prove2.me/submissions/06ee9586-fe61-4cae-9d1e-5242e1aabbce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
import Theorems.Thm_GlobalTheory_QCoh_hom_app_res
import Theorems.Thm_GlobalTheory_QCoh_pullbackSections_apply

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
theorem _root_.solution {G G' : Y.Modules} (φ : G ⟶ G') (e : U ≤ f ⁻¹ᵁ V)
    (s : Γ(G, V)) :
    ((Scheme.Modules.pullback f).map φ).app U (pullbackSections f G e s) =
      pullbackSections f G' e (φ.app V s) := by
  refine (hom_app_res ((Scheme.Modules.pullback f).map φ) e _).trans ?_
  rw [pullbackSections_apply]
  congr 1
  exact congr(($((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)).app V s).symm
end GlobalTheory.QCoh
