-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.ind_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:39.778814+00:00
-- url     : https://prove2.me/submissions/fe72eb78-0d9b-468c-870f-03b082d0ed4b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_ind_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (χ : G → ℂ) (l : (G → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ φ ∈ SB G, ∀ h, l (fun x => φ (x * h)) = χ h * l φ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) (hχ : χ k ≠ 1) :
    l (ind K) = 0 := by
  have h := hl _ (ind_mem ho hc) k
  have : (fun x => ind K (x * k)) = ind K := by
    classical
    ext x; exact if_congr (K.mul_mem_cancel_right hk) rfl rfl
  rw [this] at h
  by_contra h0
  exact hχ (mul_right_cancel₀ h0 (by rw [← h, one_mul]))
end GlobalTheory.ThK.Dbl.LD
