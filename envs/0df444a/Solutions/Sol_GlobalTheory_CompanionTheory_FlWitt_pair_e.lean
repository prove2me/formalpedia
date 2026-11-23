-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlWitt.pair_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:15.139609+00:00
-- url     : https://prove2.me/submissions/1d845274-faf8-4821-8a6d-26b45a057f1d

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_h_sum_right
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pairMap_apply

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
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) (j : Fin l)
    (p : (Fin l → L) × (Fin l → L)) : h (e j) (pairMap e f p) = p.2 j * δ := by
  rw [pairMap_apply, hh.1, h_sum_right hh, h_sum_right hh]
  simp [he, hef]
end GlobalTheory.CompanionTheory.FlWitt
