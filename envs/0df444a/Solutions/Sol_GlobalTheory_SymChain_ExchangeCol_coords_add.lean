-- Prove2me | solution 1 for GlobalTheory.SymChain.ExchangeCol.coords_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:47.807871+00:00
-- url     : https://prove2.me/submissions/053914d2-4929-458f-aa63-2fceb977c6fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixBlockColumnVanishingStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.ExchangeCol
variable {k : Type} [Field k] {ι ι' n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
namespace GlobalTheory.SymChain.ExchangeCol
theorem _root_.solution (F : LatFrame k ι (n ⊕ Fin c)) (F' : LatFrame k ι' (n' ⊕ Fin c'))
    (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) :
    F.coords F' (x + y) = F.coords F' x + F.coords F' y := by
  unfold LatFrame.coords
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl
end GlobalTheory.SymChain.ExchangeCol
