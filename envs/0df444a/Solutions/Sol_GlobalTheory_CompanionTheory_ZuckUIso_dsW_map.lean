-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckUIso.dsW_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:34.319192+00:00
-- url     : https://prove2.me/submissions/085f00b7-a25d-4de0-b60d-64d6f67d19e8

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UnitaryIso
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckUIso_ds_map
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_cons


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
theorem _root_.solution (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x))
    {v : H} (hv : IsSm G σ v) : ∀ {W : List (Mat n)}, LieW G W → dsW σ' W (e v) = e (dsW σ W v)
  | [], _ => rfl
  | X :: W, hW => by
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    rw [dsW_cons, dsW_cons, solution h e he hv hW',
      ds_map h e he (hW X List.mem_cons_self) (hv.dsW h hW')]
end GlobalTheory.CompanionTheory.ZuckUIso
