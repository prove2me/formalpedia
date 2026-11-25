-- Prove2me | solution 1 for GlobalTheory.QCoh.mono_iff_affineCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:34:33.186579+00:00
-- url     : https://prove2.me/submissions/ae896d10-feac-4887-9718-ecf08a1aeb3b

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
theorem _root_.solution (φ : M ⟶ N) : Mono φ ↔ ∀ i, Function.Injective (φ.app (𝒰 i)) := by
  refine ⟨fun _ i ↦ injective_app_of_mono φ _, fun h ↦ ?_⟩
  refine Preadditive.mono_of_isZero_kernel φ
    ((isZero_iff_affineCover 𝒰 hcov haff).mpr fun i ↦ subsingleton_of_forall_eq 0 fun s ↦ ?_)
  refine injective_kernel_ι_app φ _ (h i ?_)
  rw [(exact_kernel_ι_app φ _).apply_apply_eq_zero, map_zero, map_zero]
end GlobalTheory.QCoh
