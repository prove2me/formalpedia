-- Prove2me | solution 1 for GlobalTheory.SymChain.coords_withCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:20.719993+00:00
-- url     : https://prove2.me/submissions/bc2e3b72-84d6-4903-a453-782bd6d4d986

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Theorems.Thm_GlobalTheory_SymChain_typeFrame_bas_zero

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
omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
namespace GlobalTheory.SymChain
theorem _root_.solution (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin 0) (ord' : ι' ≃ n' ⊕ Fin (0 + 1)) (x₀ : Matrix n n' k)
    (y : n → k) : (typeFrame ϖ ord).coords (typeFrame ϖ ord') (withCol x₀ y) =
      (withCol x₀ ((ϖ : k) • y)).submatrix ord ord' := by
  unfold LatFrame.coords
  rw [typeFrame_bas_zero]
  congr 1
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply]
    · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply, Fin.eq_zero j, mul_comm]
  · exact i.elim0
end GlobalTheory.SymChain
