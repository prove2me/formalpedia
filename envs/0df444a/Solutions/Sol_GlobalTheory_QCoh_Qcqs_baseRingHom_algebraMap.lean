-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.baseRingHom_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:21.771222+00:00
-- url     : https://prove2.me/submissions/885ff341-9429-4afa-9bd6-e1787a9b740e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_comp_SpecMap

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
variable {R L : CommRingCat.{u}} [Algebra R L] (S : Submonoid R) [IsLocalization S L]
  {X Y : Scheme.{u}} {p : X ⟶ Spec R} {q : Y ⟶ Spec L} {g : Y ⟶ X}
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R L))))
include H
omit S
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution (V : Y.Opens) (r : R) :
    baseRingHom q V (algebraMap R L r) = baseRingHom (g ≫ p) V r := by
  rw [H.w, baseRingHom_comp_SpecMap]; rfl
end GlobalTheory.QCoh.Qcqs
