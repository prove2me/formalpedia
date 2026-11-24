-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlWitt.pair_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:31:44.162822+00:00
-- url     : https://prove2.me/submissions/264b019f-dd55-4d5d-9eb7-3817959e3101

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_h_sum_right
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
theorem _root_.solution (hh : IsHerm s h) {e f : Fin l → V} (he : ∀ i j, h (e i) (e j) = 0)
    (hf : ∀ i j, h (f i) (f j) = 0) (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0)
    (p r : (Fin l → L) × (Fin l → L)) :
    h (pairMap e f p) (pairMap e f r) =
      ∑ j, r.1 j * s (p.2 j * δ) + ∑ j, r.2 j * s (p.1 j * s δ) := by
  have e1 : ∀ j, h (pairMap e f p) (e j) = s (p.2 j * δ) := fun j => by
    rw [hh.2.2.1 (e j), pair_e hh he hef]
  have e2 : ∀ j, h (pairMap e f p) (f j) = s (p.1 j * s δ) := fun j => by
    rw [hh.2.2.1 (f j), pair_f hh hf hef]
  rw [pairMap_apply e f r, hh.1, h_sum_right hh, h_sum_right hh]
  simp only [e1, e2]
end GlobalTheory.CompanionTheory.FlWitt
