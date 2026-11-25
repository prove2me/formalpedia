-- Prove2me | solution 1 for GlobalTheory.QCoh.pullbackSections_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:20.912393+00:00
-- url     : https://prove2.me/submissions/d76aeea9-d3b4-4d2b-ab8e-f9577b6d0845

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
theorem _root_.solution (e : U ≤ f ⁻¹ᵁ V) (r : Γ(Y, V)) (s : Γ(G, V)) :
    pullbackSections f G e (r • s) = f.appLE V U e r • pullbackSections f G e s :=
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  (pullbackSections f G e).map_smul r s
end GlobalTheory.QCoh
