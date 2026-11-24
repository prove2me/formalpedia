-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.IsAct.comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:24.864724+00:00
-- url     : https://prove2.me/submissions/1df67642-4e8c-4b0e-91a3-26794d62a404

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj

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
theorem _root_.solution (h : IsAct ρ) (a b : O) (x : Q) : ρ a (ρ b x) = ρ b (ρ a x) := by
  rw [← h.2.1, ← h.2.1, mul_comm]
end IsAct
end GlobalTheory.HeckeCompare
