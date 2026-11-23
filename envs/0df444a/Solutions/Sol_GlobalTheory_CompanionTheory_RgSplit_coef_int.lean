-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.coef_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:59.242299+00:00
-- url     : https://prove2.me/submissions/450b4277-6715-42c8-bce0-0723d6b9b05d

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgSplit
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V] {s : L →+* L} {h : V → V → L} {δ : L} {e f : V}
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hΛ : IsLat L Λ) (hpair : ∀ x ∈ Λ, ∀ y ∈ Λ, ‖h x y‖ ≤ ‖δ‖) (heΛ : e ∈ Λ) (hfΛ : f ∈ Λ)
    {x : V} (hx : x ∈ Λ) :
    ‖ca hh δ f x‖ ≤ 1 ∧ ‖cb hh δ e x‖ ≤ 1 ∧ pr hh δ e f x ∈ Λ := by
  have hn : 0 < ‖δ‖ := norm_pos_iff.2 hδ
  have h1 : ‖ca hh δ f x‖ ≤ 1 := by
    rw [ca_apply, norm_mul, norm_inv, hs.2.1]
    exact inv_mul_le_one_of_le₀ (hpair f hfΛ x hx) hn.le
  have h2 : ‖cb hh δ e x‖ ≤ 1 := by
    rw [cb_apply, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hpair e heΛ x hx) hn.le
  refine ⟨h1, h2, ?_⟩
  rw [pr_apply]
  exact Λ.sub_mem (Λ.sub_mem hx (lat_smul_mem hΛ h1 heΛ)) (lat_smul_mem hΛ h2 hfΛ)
end GlobalTheory.CompanionTheory.RgSplit
