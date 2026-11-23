-- Prove2me | solution 1 for GlobalTheory.QCoh.resModule_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:20.844194+00:00
-- url     : https://prove2.me/submissions/2455368e-365d-461b-ae8a-f8691f890e94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution (h : V ≤ U) (r : Γ(X, U)) (s : Γ(F, V)) :
    letI := resModule F h
    r • s = X.presheaf.map (homOfLE h).op r • s := rfl
end GlobalTheory.QCoh
