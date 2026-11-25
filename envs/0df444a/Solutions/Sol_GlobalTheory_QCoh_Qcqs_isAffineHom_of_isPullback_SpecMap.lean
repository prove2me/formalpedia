-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.isAffineHom_of_isPullback_SpecMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:09:08.282546+00:00
-- url     : https://prove2.me/submissions/6f089093-9b3b-4e40-a30a-7985c00a83a3

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
variable {R L : CommRingCat.{u}} [Algebra R L] (S : Submonoid R) [IsLocalization S L]
  {X Y : Scheme.{u}} {p : X ⟶ Spec R} {q : Y ⟶ Spec L} {g : Y ⟶ X}
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R L))))
include H
omit S
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution : IsAffineHom g :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
end GlobalTheory.QCoh.Qcqs
