-- Prove2me | solution 1 for GlobalTheory.QCoh.epi_pushforward_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:19:59.208717+00:00
-- url     : https://prove2.me/submissions/c8db9cf5-274c-4ab6-b44c-b71226322e59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
import Theorems.Thm_GlobalTheory_QCoh_epi_of_locally_app_surjective
import Theorems.Thm_GlobalTheory_QCoh_app_surjective_of_epi_of_isAffineOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X Y : Scheme.{u}} {F F' : X.Modules}
variable (f : X ⟶ Y)
namespace GlobalTheory.QCoh
theorem _root_.solution [IsAffineHom f] (φ : F ⟶ F') [Epi φ] [F.IsQuasicoherent]
    [F'.IsQuasicoherent] : Epi ((Scheme.Modules.pushforward f).map φ) := by
  refine epi_of_locally_app_surjective _ fun W y hy ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy W.2
  exact ⟨V, hyV, hle, app_surjective_of_epi_of_isAffineOpen φ (IsAffineOpen.preimage hV f)⟩
end GlobalTheory.QCoh
