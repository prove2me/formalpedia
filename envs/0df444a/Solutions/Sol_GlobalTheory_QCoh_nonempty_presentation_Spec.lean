-- Prove2me | solution 1 for GlobalTheory.QCoh.nonempty_presentation_Spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:41:24.119962+00:00
-- url     : https://prove2.me/submissions/7c48cc2b-d88f-40f5-952e-dcb5e2ebb6cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
theorem _root_.solution {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] : Nonempty M.Presentation :=
  haveI := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  ⟨SheafOfModules.Presentation.ofIsIso.{u, u, u} M.fromTildeΓ
    (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _))⟩
end GlobalTheory.QCoh
