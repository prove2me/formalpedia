-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations.mem_lowIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:53:11.649442+00:00
-- url     : https://prove2.me/submissions/80f65f82-0b41-4873-bac5-a7230c610d39

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
theorem _root_.solution {D T : ℕ} {al : Fin D → ℕ} : al ∈ lowIdx D T ↔ ∑ i, al i + D < T := by
  simp only [lowIdx, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, and_iff_right_iff_imp]
  intro h i
  have := Finset.single_le_sum (f := al) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega
end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
