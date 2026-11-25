-- Prove2me | solution 1 for GlobalTheory.QCoh.res_pullbackSections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:37.150889+00:00
-- url     : https://prove2.me/submissions/c1d01bc6-d73e-4db1-8e06-4f5d20d0b457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
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
theorem _root_.solution (e : U ≤ f ⁻¹ᵁ V) (h : U' ≤ U) (s : Γ(G, V)) :
    ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE h).op (pullbackSections f G e s) =
      pullbackSections f G (h.trans e) s :=
  res_res _ _ _ _
end GlobalTheory.QCoh
