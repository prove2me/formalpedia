-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.isLocalizedModule_resBasicOpen_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:09:16.172961+00:00
-- url     : https://prove2.me/submissions/80dfeaae-cb9c-4e0a-9c6a-35ca48eb6430

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_isLocalizedModule_resBasicOpen_of_qcqs

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
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
variable [F.IsQuasicoherent]
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution [CompactSpace X] [QuasiSeparatedSpace X]
    (f : Γ(X, ⊤)) : IsLocalizedModule.Away f (resBasicOpen F f) :=
  isLocalizedModule_resBasicOpen_of_qcqs F isCompact_univ (isQuasiSeparated_univ) f
end GlobalTheory.QCoh.Qcqs
