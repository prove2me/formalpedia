-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.restrict_isLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:28:05.090806+00:00
-- url     : https://prove2.me/submissions/48aa05e2-6b76-45fb-9464-6162c15a67e3

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_smul_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_absorb
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_bdd
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_latOf_isLat
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_coef_eq

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
theorem _root_.solution (hS : StSandwich) [ProperSpace L] [FiniteDimensional L V]
    (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0) (hef : h e f = δ)
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) {Λ : AddSubgroup V} (hΛ : IsLat L Λ) :
    IsLat L (Λ.comap U.subtype.toAddMonoidHom) := by
  have lat0 := latOf_isLat (Module.finBasis L U)
  obtain ⟨c, hc0, -, hc⟩ := lat_bdd hΛ lat0 (prU hh hδ he hf hef hU)
  refine hS L U _ _ c lat0 hc0 (fun x hx => ?_) (fun x => ?_) (fun a ha x hx => ?_)
  · have hx' := (hU x).1 x.2
    have hp : prU hh hδ he hf hef hU (x : V) = x := by
      apply Subtype.ext
      have := (coef_eq hh hδ he hf hef 0 0 hx'.1 hx'.2).2.2
      simpa [prU] using this
    have := hc x hx
    rwa [hp] at this
  · obtain ⟨a, ha0, -, ha⟩ := lat_absorb hΛ (fun _ : Unit => (x : V))
    exact ⟨a, ha0, ha ()⟩
  · exact lat_smul_mem hΛ ha hx
end GlobalTheory.CompanionTheory.RgSplit
