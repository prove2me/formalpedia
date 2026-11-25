-- Prove2me | solution 1 for GlobalTheory.QCoh.isIso_iff_affineCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:47:27.333859+00:00
-- url     : https://prove2.me/submissions/2db7d9d0-6263-4c11-aa54-97d6069754a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Theorems.Thm_GlobalTheory_QCoh_mono_iff_affineCover
import Theorems.Thm_GlobalTheory_QCoh_epi_iff_affineCover

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
variable {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i))
include hcov haff
variable [M.IsQuasicoherent] [N.IsQuasicoherent]
namespace GlobalTheory.QCoh
theorem _root_.solution (φ : M ⟶ N) : IsIso φ ↔ ∀ i, Function.Bijective (φ.app (𝒰 i)) := by
  rw [isIso_iff_mono_and_epi, mono_iff_affineCover 𝒰 hcov haff, epi_iff_affineCover 𝒰 hcov haff,
    ← forall_and]
  rfl
end GlobalTheory.QCoh
