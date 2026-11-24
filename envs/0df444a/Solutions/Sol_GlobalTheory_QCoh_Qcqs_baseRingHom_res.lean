-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.baseRingHom_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:52.555799+00:00
-- url     : https://prove2.me/submissions/b062cd93-4843-4e10-a05c-bde505d9d695

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
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution (p : X ⟶ Spec R) {U V : X.Opens} (h : V ≤ U) (r : R) :
    X.presheaf.map (homOfLE h).op (baseRingHom p U r) = baseRingHom p V r := by
  rw [← ConcreteCategory.comp_apply, baseRingHom, Category.assoc, Scheme.Hom.appLE_map]
  rfl
end GlobalTheory.QCoh.Qcqs
