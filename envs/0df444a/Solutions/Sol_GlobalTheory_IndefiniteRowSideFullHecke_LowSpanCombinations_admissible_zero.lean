-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations.admissible_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:52:58.056011+00:00
-- url     : https://prove2.me/submissions/9fdc49db-9fef-42f1-8095-e664126d1b6e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_LowSpanCombinations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
theorem _root_.solution (X : Data E r) : Admissible X (fun _ => 0) 0 :=
  ⟨le_rfl, ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩, 0,
    fun _ _ => ⟨0, fun _ _ _ _ _ => by simp⟩, 0, fun _ _ => by simp⟩
end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
