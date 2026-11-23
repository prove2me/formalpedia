-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.appLinearBase_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:33.85135+00:00
-- url     : https://prove2.me/submissions/cd05e252-9b47-45f6-8134-bb9bd6d8e7f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap

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
variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution (p : X ⟶ Spec R) (g : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (U : X.Opens) (s : Γ(F, U)) :
    appLinearBase p g φ U s = φ.app U s := rfl
end GlobalTheory.QCoh.Qcqs
