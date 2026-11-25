-- Prove2me | solution 1 for GlobalTheory.SymChain.typeFrame_bas_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:34.677316+00:00
-- url     : https://prove2.me/submissions/bd349e49-b0e2-4242-ac5f-a7a163166301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] {ι ι' n n' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
omit [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SymChain
theorem _root_.solution (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin 0) : (typeFrame ϖ ord).bas = 1 := by
  apply Units.ext
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [typeFrame, embA, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0
end GlobalTheory.SymChain
