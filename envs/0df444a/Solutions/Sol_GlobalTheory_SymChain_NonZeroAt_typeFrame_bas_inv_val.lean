-- Prove2me | solution 1 for GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_inv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:05.4338+00:00
-- url     : https://prove2.me/submissions/fd17d478-8b74-43fd-8f60-d861c2028b3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_StandardOrderSymmInr
import Theorems.Thm_GlobalTheory_SymChain_NonZeroAt_typeFrame_bas_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.NonZeroAt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SymChain.NonZeroAt
theorem _root_.solution (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_bas_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases i with i | i
  · simp
  · simp [mul_inv_cancel₀, pow_ne_zero]
end GlobalTheory.SymChain.NonZeroAt
