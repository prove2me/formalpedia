-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.isLocalizedModule_resBasicOpen_of_qcqs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:33:01.944212+00:00
-- url     : https://prove2.me/submissions/12ff9e80-554a-41a1-bec6-a6a62a8e1877

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_pow_smul_eq_zero_of_isCompact
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_pow_smul_eq_res_of_qcqs
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen_iff


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
theorem _root_.solution (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (resBasicOpen F f) :=
  (isLocalizedModule_resBasicOpen_iff F f).mpr
    ⟨exists_pow_smul_eq_res_of_qcqs F hU hU' f _ rfl,
      exists_pow_smul_eq_zero_of_isCompact F hU f _ rfl⟩
end GlobalTheory.QCoh.Qcqs
