-- Prove2me | solution 1 for GlobalTheory.QCoh.exact_iff_forall_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:06:27.704966+00:00
-- url     : https://prove2.me/submissions/6c6a374c-1d42-48ff-96fa-9c18f001de1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Theorems.Thm_GlobalTheory_QCoh_exact_iff_affineCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
variable [M.IsQuasicoherent] [N.IsQuasicoherent]
variable (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
  [S.X₃.IsQuasicoherent]
namespace GlobalTheory.QCoh
theorem _root_.solution :
    S.Exact ↔ ∀ U, IsAffineOpen U → Function.Exact (S.f.app U) (S.g.app U) :=
  (exact_iff_affineCover (fun i : X.affineOpens ↦ i.1) (iSup_affineOpens_eq_top X)
    (fun i ↦ i.2) S).trans Subtype.forall
end GlobalTheory.QCoh
