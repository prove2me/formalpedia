-- Prove2me | solution 1 for GlobalTheory.QCoh.nonempty_presentation_over_of_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:41:24.891846+00:00
-- url     : https://prove2.me/submissions/ce3c5881-d2cc-46f8-99c2-ab92c6bfee72

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
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
theorem _root_.solution (P : (F.restrict U.ι).Presentation) :
    Nonempty (F.over U).Presentation := by
  let e := Scheme.Modules.overEquiv U
  have : Limits.PreservesColimitsOfSize.{u, u} e.inverse := inferInstance
  let iso : e.inverse.obj (F.restrict U.ι) ≅ F.over U :=
    e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app F).symm ≪≫
      (e.unitIso.app (F.over U)).symm
  exact ⟨SheafOfModules.Presentation.ofIsIso.{u, u, u} iso.hom
    (P.map e.inverse (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm)⟩
end GlobalTheory.QCoh
