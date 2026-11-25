-- Prove2me | solution 1 for GlobalTheory.LatClass.aff_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:28.301145+00:00
-- url     : https://prove2.me/submissions/4e5005ce-6f27-4228-a394-9939d661f9e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n] [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.LatClass
theorem _root_.solution (x₀ : Matrix n n' k) (y) (w : n' → k) (s : k) :
    affPt (c := c + 1) 1 x₀ y *ᵥ Sum.elim w (Pi.single 0 s) = Sum.elim (x₀ *ᵥ w) (Pi.single 0 s) := by
  ext (r | l)
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, affPt, basePt, Free, Pi.single_apply]
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, affPt, basePt, Free, Pi.single_apply]
end GlobalTheory.LatClass
