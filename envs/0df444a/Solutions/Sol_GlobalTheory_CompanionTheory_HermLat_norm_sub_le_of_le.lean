-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermLat.norm_sub_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:19.631041+00:00
-- url     : https://prove2.me/submissions/bf70b4b6-6f18-4e0b-9465-3d55a9d95778

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermLat
theorem _root_.solution {a b : L} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by simpa using hb))
end GlobalTheory.CompanionTheory.HermLat
