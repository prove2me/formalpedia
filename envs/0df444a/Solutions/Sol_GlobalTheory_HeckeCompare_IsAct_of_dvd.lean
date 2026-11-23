-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.IsAct.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:18.491822+00:00
-- url     : https://prove2.me/submissions/c8422ca0-4a1e-4a9c-885e-38fc7dcc2ffa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {O Q : Type} [CommRing O] [CommGroup Q] {ρ : O → Q →* Q}
namespace GlobalTheory.HeckeCompare
namespace IsAct
theorem _root_.solution (h : IsAct ρ) {n : ℕ} {x : Q} (hx : x ^ n = 1) {a : O} (ha : (n : O) ∣ a) : ρ a x = 1 := by
  obtain ⟨b, rfl⟩ := ha
  rw [h.2.1, h.nat, hx, map_one]
end IsAct
end GlobalTheory.HeckeCompare
