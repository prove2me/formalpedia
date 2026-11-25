-- Prove2me | solution 1 for GlobalTheory.LatClass.N_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:13.03905+00:00
-- url     : https://prove2.me/submissions/ba6bb6fa-89ab-408c-8f87-c502266d3e0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_LatClass_N_mulVec

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
theorem _root_.solution {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1) (y : n ⊕ Fin c → k)
    (h : ∀ l : Fin c, 0 < l.val → y (.inr l) = 0) : u.val *ᵥ y = y := by
  ext r
  refine N_mulVec hu y r ?_
  rintro (s | s) hs
  · rcases r with r | r <;> simp [lev] at hs
  · apply h
    rcases r with r | r <;> simp [lev] at hs <;> omega
end GlobalTheory.LatClass
