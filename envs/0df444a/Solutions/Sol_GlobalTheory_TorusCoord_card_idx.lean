-- Prove2me | solution 1 for GlobalTheory.TorusCoord.card_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:30.054896+00:00
-- url     : https://prove2.me/submissions/09c50754-4dbe-4180-b391-24218f7285d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Theorems.Thm_GlobalTheory_TorusCoord_sum_emb_split
import Theorems.Thm_GlobalTheory_TorusCoord_dimOf_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.TorusCoord
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.TorusCoord
theorem _root_.solution (X : Data E r) : Fintype.card (Idx (dimOf X)) = X.Ψ.card * r := by
  rw [Fintype.card_sigma, sum_emb_split X]
  simp [dimOf_add]
end GlobalTheory.TorusCoord
