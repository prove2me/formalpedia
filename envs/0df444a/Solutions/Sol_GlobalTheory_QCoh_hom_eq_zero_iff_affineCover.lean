-- Prove2me | solution 1 for GlobalTheory.QCoh.hom_eq_zero_iff_affineCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:12:58.916801+00:00
-- url     : https://prove2.me/submissions/d21db990-3e3a-4ec9-8bc7-ac67e4250a51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
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
namespace GlobalTheory.QCoh
theorem _root_.solution {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰)
    (haff : ∀ i, IsAffineOpen (𝒰 i)) [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    φ = 0 ↔ ∀ i s, φ.app (𝒰 i) s = 0 := by
  refine ⟨fun h i s ↦ by rw [h]; rfl, fun h ↦ ?_⟩
  have : Epi (kernel.ι φ) := (epi_iff_affineCover 𝒰 hcov haff _).mpr fun i s ↦
    (exact_kernel_ι_app φ _ s).mp (h i s)
  rw [← cancel_epi (kernel.ι φ), kernel.condition, comp_zero]
end GlobalTheory.QCoh
