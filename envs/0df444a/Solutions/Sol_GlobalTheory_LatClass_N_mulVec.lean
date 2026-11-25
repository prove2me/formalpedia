-- Prove2me | solution 1 for GlobalTheory.LatClass.N_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:57:34.16813+00:00
-- url     : https://prove2.me/submissions/38817acc-57b8-473f-be02-f421be2cb7b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff


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
omit [ValuativeRel k]
namespace GlobalTheory.LatClass
theorem _root_.solution {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (y : n ⊕ Fin c → k) (r : n ⊕ Fin c)
    (h : ∀ s, lev p r < lev p s → y s = 0) : (u.val *ᵥ y) r = y r := by
  have hu' := (Radical.mem_N_iff u).1 hu
  conv_rhs => rw [← one_mulVec y]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases le_or_gt (lev p s) (lev p r) with hs | hs
  · exact congrArg (· * y s) (hu' r s hs)
  · simp [h s hs]
end GlobalTheory.LatClass
