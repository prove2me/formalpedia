-- Prove2me | solution 1 for GlobalTheory.LatClass.topCoord_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:54.212886+00:00
-- url     : https://prove2.me/submissions/f3ea80aa-1255-4662-bf4a-e2e7bdf96593

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_LatClass_topCoord_le

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
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.LatClass
theorem _root_.solution {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c 1) (h : GL (n ⊕ Fin c) k) (i : Fin c) :
    topCoord (latOf (r * h)) i = topCoord (latOf h) i := by
  refine Set.Subset.antisymm ?_ (topCoord_le hr h i)
  have := topCoord_le (inv_mem hr) (r * h) i
  rwa [inv_mul_cancel_left] at this
end GlobalTheory.LatClass
