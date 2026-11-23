-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.baseRingHom_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:37.333805+00:00
-- url     : https://prove2.me/submissions/cb5d8c78-1e82-4987-a83b-5a484378d052

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
theorem _root_.solution (p : X ⟶ Spec R) :
    baseRingHom p ⊤ = (Scheme.ΓSpecIso R).inv ≫ p.appTop := by
  rw [baseRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl
end GlobalTheory.QCoh.Qcqs
