-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.baseRingHom_comp_SpecMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:00.470845+00:00
-- url     : https://prove2.me/submissions/1966737e-2247-41ae-a773-2a09efebeb6d

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
theorem _root_.solution {L : CommRingCat.{u}} (q : Y ⟶ Spec L) (ι : R ⟶ L)
    (V : Y.Opens) : baseRingHom (q ≫ Spec.map ι) V = ι ≫ baseRingHom q V := by
  rw [baseRingHom, baseRingHom, Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  exact congrArg _ (Scheme.Hom.appLE_comp_appLE q (Spec.map ι) ⊤ ⊤ V le_top le_top).symm
end GlobalTheory.QCoh.Qcqs
