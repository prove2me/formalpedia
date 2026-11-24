-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.MaxLat.IsLat.smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:08:25.612771+00:00
-- url     : https://prove2.me/submissions/c1125561-38b3-4398-8bc0-c7a08ff6cefe

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.MaxLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.RgFl.MaxLat
namespace IsLat
theorem _root_.solution {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {a : L} (ha : ‖a‖ ≤ 1) {x : V}
    (hx : x ∈ Λ) : a • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  simpa using mul_le_one₀ ha (norm_nonneg _) (hx i)
end IsLat
end GlobalTheory.CompanionTheory.RgFl.MaxLat
