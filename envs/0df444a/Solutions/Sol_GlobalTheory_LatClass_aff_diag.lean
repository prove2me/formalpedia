-- Prove2me | solution 1 for GlobalTheory.LatClass.aff_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:32.80626+00:00
-- url     : https://prove2.me/submissions/e1429dce-1c73-4142-a4c5-b293be140cf2

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
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.LatClass
theorem _root_.solution (x₀ : Matrix n n' k) (y) (i l : Fin c) (h : i ≤ l) :
    affPt (c := c) 1 x₀ y (.inr l) (.inr i.castSucc) = if l = i then 1 else 0 := by
  have : ¬ l < i := not_lt.2 h
  simp [affPt, basePt, Free, this, Fin.ext_iff]
end GlobalTheory.LatClass
