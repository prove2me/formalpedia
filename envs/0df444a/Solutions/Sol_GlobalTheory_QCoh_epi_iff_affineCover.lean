-- Prove2me | solution 1 for GlobalTheory.QCoh.epi_iff_affineCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:30:16.745799+00:00
-- url     : https://prove2.me/submissions/d4af6b10-eb1b-49a8-9b60-bfa659a80a61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Theorems.Thm_GlobalTheory_QCoh_isZero_iff_affineCover

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
theorem _root_.solution (φ : M ⟶ N) : Epi φ ↔ ∀ i, Function.Surjective (φ.app (𝒰 i)) := by
  refine ⟨fun _ i ↦ surjective_app_of_epi φ (haff i), fun h ↦ ?_⟩
  refine Preadditive.epi_of_isZero_cokernel φ
    ((isZero_iff_affineCover 𝒰 hcov haff).mpr fun i ↦ subsingleton_of_forall_eq 0 fun s ↦ ?_)
  obtain ⟨t, rfl⟩ := surjective_cokernel_π_app φ (haff i) s
  obtain ⟨t, rfl⟩ := h i t
  exact (exact_cokernel_π_app φ (haff i)).apply_apply_eq_zero t
end GlobalTheory.QCoh
