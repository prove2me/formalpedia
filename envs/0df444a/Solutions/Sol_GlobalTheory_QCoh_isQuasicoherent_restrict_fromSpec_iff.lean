-- Prove2me | solution 1 for GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:34:22.238926+00:00
-- url     : https://prove2.me/submissions/d79c585a-0251-438b-95f5-7bc8b39802f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isLocalizing_restrict_fromSpec_iff

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
namespace GlobalTheory.QCoh
theorem _root_.solution (hU : IsAffineOpen U) :
    (F.restrict hU.fromSpec).IsQuasicoherent ↔
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f) := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing,
    isLocalizing_restrict_fromSpec_iff]
end GlobalTheory.QCoh
