-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.frame_flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:27.983334+00:00
-- url     : https://prove2.me/submissions/dbc0344f-b5e1-4e02-ab48-1f4efd373267

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_adapted_flip
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_hermitian_frame_partial_flip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
variable {s : L →+* L} {δ : L} {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h)
    {u : Fin l → L} {Λ Λ' : AddSubgroup V} (hF : IsFrame h δ e f W)
    (h1 : IsAdapted h e f W (fun _ => 1) Λ) (h2 : IsAdapted h e f W u Λ') (p : L) (n : Fin l → ℤ)
    (hn : ∀ i, ‖u i‖ = ‖p‖ ^ n i) (hp0 : p ≠ 0) :
    ∃ (e' f' : Fin l → V) (m : Fin l → ℕ), IsFrame h δ e' f' W ∧ IsAdapted h e' f' W (fun _ => 1) Λ ∧
      IsAdapted h e' f' W (fun i => p ^ m i) Λ' := by
  have hsδ : s δ ≠ 0 := (map_ne_zero s).2 hδ
  have hc : ‖δ / s δ‖ = 1 := by
    rw [norm_div, hs.2.1, div_self (norm_ne_zero_iff.2 hδ)]
  refine ⟨_, _, fun i => (n i).natAbs, hermitian_frame_partial_flip hs hδ hh hF (fun i => n i < 0),
    adapted_flip (fun i => n i < 0) hc (fun i => ?_) h1, adapted_flip (fun i => n i < 0) hc (fun i => ?_) h2⟩
  · simp
  · rw [hn i, norm_pow]
    have hpp : ‖p‖ ≠ 0 := norm_ne_zero_iff.2 hp0
    by_cases hi : n i < 0
    · rw [if_pos hi, ← zpow_neg, ← zpow_natCast]
      congr 1
      beta_reduce
      omega
    · rw [if_neg hi, ← zpow_natCast]
      congr 1
      beta_reduce
      omega
end GlobalTheory.CompanionTheory.FlDecomp
