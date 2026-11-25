-- Prove2me | solution 1 for GlobalTheory.LatClass.aff_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:51.879858+00:00
-- url     : https://prove2.me/submissions/1cf61011-3457-429e-a1ee-7aebb4052207

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
theorem _root_.solution (x₀ : Matrix n n' k) (y) (w : n' → k) (i : Fin (c + 1)) (s : k) (l : Fin c) :
    (affPt (c := c) 1 x₀ y *ᵥ Sum.elim w (Pi.single i s)) (.inr l) = affPt 1 x₀ y (.inr l) (.inr i) * s := by
  have : ∀ r, affPt (c := c) 1 x₀ y (.inr l) (.inl r) = 0 := fun r => by simp [affPt, basePt, Free]
  simp [mulVec, dotProduct, Fintype.sum_sum_type, this, Pi.single_apply]
end GlobalTheory.LatClass
