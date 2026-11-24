-- Prove2me | solution 1 for GlobalTheory.DegreeGrowth.finrank_boxSpan_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:17.172241+00:00
-- url     : https://prove2.me/submissions/52fe872e-13c0-46f8-9a37-236d42213a7d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.DegreeGrowth
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]
namespace GlobalTheory.DegreeGrowth
theorem _root_.solution {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D : ℕ) :
    Module.finrank K (boxSpan K y b D) ≤ (D + 1) ^ s * n := by
  have := finrank_range_le_card (R := K) (fun al : (Fin s → Fin (D + 1)) × Fin n =>
    (∏ i, y i ^ (al.1 i : ℕ)) * b al.2)
  refine le_trans this ?_
  simp
end GlobalTheory.DegreeGrowth
