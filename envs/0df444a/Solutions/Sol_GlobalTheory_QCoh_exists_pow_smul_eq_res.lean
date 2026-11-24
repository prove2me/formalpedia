-- Prove2me | solution 1 for GlobalTheory.QCoh.exists_pow_smul_eq_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:25.538571+00:00
-- url     : https://prove2.me/submissions/f285f213-1ba7-4d6a-99fd-833912f43cca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen_iff
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen

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
variable [F.IsQuasicoherent]
namespace GlobalTheory.QCoh
theorem _root_.solution (hU : IsAffineOpen U) (f : Γ(X, U)) (h : V ≤ U)
    (hV : V = X.basicOpen f) (s : Γ(F, V)) :
    ∃ (n : ℕ) (t : Γ(F, U)),
      X.presheaf.map (homOfLE h).op f ^ n • s = F.presheaf.map (homOfLE h).op t := by
  subst hV
  exact ((isLocalizedModule_resBasicOpen_iff F f).mp (isLocalizedModule_resBasicOpen F hU f)).1 s
end GlobalTheory.QCoh
