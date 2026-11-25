-- Prove2me | solution 1 for GlobalTheory.QCoh.isQuasicoherent_iff_forall_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:42:36.331839+00:00
-- url     : https://prove2.me/submissions/10ef1644-9c87-436e-a36b-467d01e7a794

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_forall_exists_affine

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
theorem _root_.solution :
    F.IsQuasicoherent ↔ ∀ U : X.Opens, IsAffineOpen U →
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f) := by
  refine ⟨fun _ U hU f ↦ isLocalizedModule_resBasicOpen F hU f, fun h ↦ ?_⟩
  refine isQuasicoherent_of_forall_exists_affine F fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, hU, hx, h U hU⟩
end GlobalTheory.QCoh
