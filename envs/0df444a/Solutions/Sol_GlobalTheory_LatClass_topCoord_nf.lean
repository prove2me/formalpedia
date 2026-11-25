-- Prove2me | solution 1 for GlobalTheory.LatClass.topCoord_nf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:47.070185+00:00
-- url     : https://prove2.me/submissions/80de367d-54ac-4825-9e11-d74f363501b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_LatClass_mem_nf
import Theorems.Thm_GlobalTheory_LatClass_col_mem_nf

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
theorem _root_.solution (g : GL n k) (e : Fin (c + 1) → ℤ) (z : n → k) (i : Fin (c + 1)) :
    topCoord (latOf (nfBasis ϖ g e z)) i = powInt ϖ (e i) := by
  ext s
  constructor
  · rintro ⟨y, hy, -, rfl⟩
    exact (mem_nf.1 hy).2 i
  · intro hs
    exact ⟨_, col_mem_nf i hs, fun l hl => by simp [hl.ne'], by simp⟩
end GlobalTheory.LatClass
