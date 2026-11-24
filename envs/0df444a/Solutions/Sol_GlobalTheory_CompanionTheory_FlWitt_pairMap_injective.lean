-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlWitt.pairMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:31:41.746934+00:00
-- url     : https://prove2.me/submissions/d5837643-6c54-43db-820a-443caa0d6ce5

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_h_zero_right
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pair_e
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pair_f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlWitt
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ}
namespace GlobalTheory.CompanionTheory.FlWitt
theorem _root_.solution (hh : IsHerm s h) (hd : δ ≠ 0) {e f : Fin l → V}
    (he : ∀ i j, h (e i) (e j) = 0) (hf : ∀ i j, h (f i) (f j) = 0)
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) :
    Function.Injective (pairMap e f : ((Fin l → L) × (Fin l → L)) →ₗ[L] V) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  have hb : ∀ j, p.2 j = 0 := fun j => by
    have := pair_e hh he hef j p
    rw [hp, h_zero_right hh] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hd
  have ha : ∀ j, p.1 j = 0 := fun j => by
    have := pair_f hh hf hef j p
    rw [hp, h_zero_right hh] at this
    exact (mul_eq_zero.1 this.symm).resolve_right ((map_ne_zero s).2 hd)
  exact Prod.ext (funext ha) (funext hb)
end GlobalTheory.CompanionTheory.FlWitt
