-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.coef_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:52.048969+00:00
-- url     : https://prove2.me/submissions/1475a40e-3860-4c12-8e4b-c20fde829037

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing

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
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
variable {δ : L} {e f : V}
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0)
    (hef : h e f = δ) (a b : L) {w : V} (hew : h e w = 0) (hfw : h f w = 0) :
    ca hh δ f (a • e + b • f + w) = a ∧ cb hh δ e (a • e + b • f + w) = b ∧
      pr hh δ e f (a • e + b • f + w) = w := by
  have hsδ : s δ ≠ 0 := (map_ne_zero s).2 hδ
  have hfe := h_fe hh hef
  have h1 : ca hh δ f (a • e + b • f + w) = a := by
    rw [ca_apply, hh.1, hh.1, hh.2.1, hh.2.1, hf, hfe, hfw]
    field_simp
    simp
  have h2 : cb hh δ e (a • e + b • f + w) = b := by
    rw [cb_apply, hh.1, hh.1, hh.2.1, hh.2.1, he, hef, hew]
    field_simp
    simp
  refine ⟨h1, h2, ?_⟩
  rw [pr_apply, h1, h2]
  abel
end GlobalTheory.CompanionTheory.RgSplit
