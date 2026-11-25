-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckUIso.ds_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:29:53.18428+00:00
-- url     : https://prove2.me/submissions/5f0208c5-908d-4e39-ba3e-fda4dd86299f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UnitaryIso
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_differentiableAt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_hasDerivAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckUIso
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk dsigW)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup H'] [NormedSpace ℂ H']
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}
namespace GlobalTheory.CompanionTheory.ZuckUIso
theorem _root_.solution (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) : ds σ' X (e v) = e (ds σ X v) := by
  have h1 := (e.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hv.differentiableAt h hX).hasDerivAt
  have h2 : (fun t => σ' (ex X t) (e v)) = (e.restrictScalars ℝ) ∘ fun t => σ (ex X t) v := by
    ext t; exact (he _ (hX t) v).symm
  unfold ds
  rw [h2, h1.deriv]; rfl
end GlobalTheory.CompanionTheory.ZuckUIso
