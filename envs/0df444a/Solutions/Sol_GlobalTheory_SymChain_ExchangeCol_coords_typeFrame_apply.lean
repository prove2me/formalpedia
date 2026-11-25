-- Prove2me | solution 1 for GlobalTheory.SymChain.ExchangeCol.coords_typeFrame_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:49.856866+00:00
-- url     : https://prove2.me/submissions/320dde58-93bc-4f03-829c-7bfac61033e5

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
theorem _root_.solution (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (typeFrame ϖ o).coords (typeFrame ϖ o') x a b =
      Sum.elim (fun _ => 1) (fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) (o a) * x (o a) (o' b) *
        Sum.elim (fun _ => 1) (fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) (o' b) := by
  have e : ((typeFrame ϖ o).bas⁻¹).val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change fromBlocks 1 0 0 (diagonal _) * _ = _
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have e' : (typeFrame ϖ o').bas.val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) := rfl
  unfold LatFrame.coords
  rw [e, e', ← diagonal_one, ← diagonal_one, fromBlocks_diagonal, fromBlocks_diagonal, submatrix_apply,
    mul_diagonal, diagonal_mul]
  rfl
end GlobalTheory.SymChain.ExchangeCol
