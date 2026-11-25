-- Prove2me | solution 1 for GlobalTheory.QCoh.exact_app_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:28.545232+00:00
-- url     : https://prove2.me/submissions/636d4b4f-998e-4a19-8812-0b8031a3128c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Theorems.Thm_GlobalTheory_QCoh_exact_app_iff_surjective_lift

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
namespace GlobalTheory.QCoh
theorem _root_.solution {S : ShortComplex X.Modules} (hS : S.Exact) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (hU : IsAffineOpen U) :
    Function.Exact (S.f.app U) (S.g.app U) :=
  haveI := (S.exact_iff_epi_kernel_lift).mp hS
  (exact_app_iff_surjective_lift S U).mpr (surjective_app_of_epi _ hU)
end GlobalTheory.QCoh
