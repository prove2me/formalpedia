-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.app_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:17.809883+00:00
-- url     : https://prove2.me/submissions/4551cf56-23cf-4511-b7cb-135e59d11cba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) {U V W : X.Opens}
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution (h : V ≤ W) (s : Γ(F, W)) :
    φ.app V (F.presheaf.map (homOfLE h).op s) = G.presheaf.map (homOfLE h).op (φ.app W s) :=
  congr($(φ.mapPresheaf.naturality (homOfLE h).op) s)
end GlobalTheory.QCoh.Qcqs
