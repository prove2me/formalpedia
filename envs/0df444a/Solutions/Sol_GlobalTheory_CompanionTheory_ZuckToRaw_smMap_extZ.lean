-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckToRaw.smMap_extZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:28.115925+00:00
-- url     : https://prove2.me/submissions/48d065e6-2c95-410d-a065-c0fb7391d773

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ToRawComplex
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckToRaw_extZ_coe
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckToRaw
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckToRaw
theorem _root_.solution {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub)
    (hf : ∀ W, LieWd k r W → ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))), (∀ W' ∈ Ws, LieWd k r W') ∧
      ∀ y : R.smSub, ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (f y : R'.H)‖ ≤
        C * (Ws.map fun W' => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W' (y : R.H)‖).sum) :
    SmMap R R' (extZ f) where
  mem v hv := by
    have := extZ_coe f ⟨v, hv⟩
    rw [show extZ f v = _ from this]
    exact (f _).2
  add v hv w hw := by
    have h1 := extZ_coe f ⟨v, hv⟩
    have h2 := extZ_coe f ⟨w, hw⟩
    have h3 := extZ_coe f (⟨v, hv⟩ + ⟨w, hw⟩)
    rw [show extZ f v = _ from h1, show extZ f w = _ from h2, show extZ f (v + w) = _ from h3, map_add]
    rfl
  smul a v hv := by
    have h1 := extZ_coe f ⟨v, hv⟩
    have h3 := extZ_coe f (a • ⟨v, hv⟩)
    rw [show extZ f v = _ from h1, show extZ f (a • v) = _ from h3, map_smul]
    rfl
  cont W hW := by
    obtain ⟨C, Ws, h1, h2⟩ := hf W hW
    refine ⟨C, Ws, h1, fun v hv => ?_⟩
    have h3 := extZ_coe f ⟨v, hv⟩
    show ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (extZ f v)‖ ≤ _
    rw [show extZ f v = _ from h3]
    exact h2 ⟨v, hv⟩
end GlobalTheory.CompanionTheory.ZuckToRaw
