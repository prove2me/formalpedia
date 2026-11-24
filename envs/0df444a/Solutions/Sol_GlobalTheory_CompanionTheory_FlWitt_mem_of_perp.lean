-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlWitt.mem_of_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:31:39.83779+00:00
-- url     : https://prove2.me/submissions/ce1c6d02-3c3f-45a2-be00-5b85e89eb225

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pairMap_apply
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
theorem _root_.solution (hh : IsHerm s h) (hd : δ ≠ 0) {e f : Fin l → V} {W : Submodule L V}
    (F : IsFrame h δ e f W) (x : V) (h1 : ∀ i, h (e i) x = 0) (h2 : ∀ i, h (f i) x = 0) : x ∈ W := by
  obtain ⟨he, hf, hef, hW, -, hdec⟩ := F
  obtain ⟨a, b, w, hw, rfl⟩ := hdec x
  have hx : ∑ i, a i • e i + ∑ i, b i • f i = pairMap e f (a, b) := rfl
  rw [hx] at h1 h2 ⊢
  have hb : ∀ j, b j = 0 := fun j => by
    have := h1 j
    rw [hh.1, pair_e hh he hef, (hW w hw j).1, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_right hd
  have ha : ∀ j, a j = 0 := fun j => by
    have := h2 j
    rw [hh.1, pair_f hh hf hef, (hW w hw j).2, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_right ((map_ne_zero s).2 hd)
  have h0 : pairMap e f (a, b) = 0 := by
    rw [pairMap_apply]
    simp [ha, hb]
  rw [h0, zero_add]
  exact hw
end GlobalTheory.CompanionTheory.FlWitt
