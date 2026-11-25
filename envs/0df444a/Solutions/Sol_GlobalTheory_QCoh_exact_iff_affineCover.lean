-- Prove2me | solution 1 for GlobalTheory.QCoh.exact_iff_affineCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:05.937037+00:00
-- url     : https://prove2.me/submissions/4dab4e27-9e98-4651-a510-5efba23893cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Theorems.Thm_GlobalTheory_QCoh_exact_app_iff_surjective_lift
import Theorems.Thm_GlobalTheory_QCoh_epi_iff_affineCover
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
variable {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i))
include hcov haff
variable [M.IsQuasicoherent] [N.IsQuasicoherent]
variable (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
  [S.X₃.IsQuasicoherent]
namespace GlobalTheory.QCoh
theorem _root_.solution :
    S.Exact ↔ ∀ i, Function.Exact (S.f.app (𝒰 i)) (S.g.app (𝒰 i)) := by
  simp only [S.exact_iff_epi_kernel_lift, epi_iff_affineCover 𝒰 hcov haff,
    exact_app_iff_surjective_lift]
end GlobalTheory.QCoh
