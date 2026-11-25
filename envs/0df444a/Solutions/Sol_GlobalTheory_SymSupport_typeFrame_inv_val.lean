-- Prove2me | solution 1 for GlobalTheory.SymSupport.typeFrame_inv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:38.787077+00:00
-- url     : https://prove2.me/submissions/ea5f61a3-c51b-42fb-a07b-0b9eeed0d9e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Theorems.Thm_GlobalTheory_SymSupport_typeFrame_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymSupport
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymSupport
theorem _root_.solution {ι : Type*} (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => 1) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp
end GlobalTheory.SymSupport
