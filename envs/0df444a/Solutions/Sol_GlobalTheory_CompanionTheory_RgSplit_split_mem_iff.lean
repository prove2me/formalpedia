-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.split_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:12:09.354977+00:00
-- url     : https://prove2.me/submissions/89b6433f-2b3e-4c84-b9e0-2e88b762d8a2

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_smul_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_coef_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_coef_int

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
variable {U : Submodule L V}
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h) (he : h e e = 0)
    (hf : h f f = 0) (hef : h e f = δ) {Λ : AddSubgroup V} (hΛ : IsLat L Λ)
    (hpair : ∀ x ∈ Λ, ∀ y ∈ Λ, ‖h x y‖ ≤ ‖δ‖) (heΛ : e ∈ Λ) (hfΛ : f ∈ Λ) (a b : L) {w : V}
    (hew : h e w = 0) (hfw : h f w = 0) :
    a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ w ∈ Λ := by
  constructor
  · intro hx
    obtain ⟨c1, c2, c3⟩ := coef_eq hh hδ he hf hef a b hew hfw
    have := coef_int hs hδ hh hΛ hpair heΛ hfΛ hx
    rwa [c1, c2, c3] at this
  · rintro ⟨h1, h2, h3⟩
    exact Λ.add_mem (Λ.add_mem (lat_smul_mem hΛ h1 heΛ) (lat_smul_mem hΛ h2 hfΛ)) h3
end GlobalTheory.CompanionTheory.RgSplit
