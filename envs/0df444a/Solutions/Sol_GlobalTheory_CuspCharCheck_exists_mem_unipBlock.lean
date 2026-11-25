-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.exists_mem_unipBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:59.087666+00:00
-- url     : https://prove2.me/submissions/d31e2a3d-0d66-496b-99e6-a9492b84a027

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
namespace GlobalTheory.CuspCharCheck
theorem _root_.solution (d a : ℕ) (X : Matrix (Fin d) (Fin d) F)
    (hX : ∀ i j : Fin d, ¬ (i.val < a ∧ a ≤ j.val) → X i j = 0) :
    ∃ u ∈ (unipBlock d a : Set (GL (Fin d) F)), (u : Matrix (Fin d) (Fin d) F) = 1 + X := by
  have h0 := block_mul_eq_zero hX hX
  refine ⟨⟨1 + X, 1 - X, ?_, ?_⟩, (mem_unipBlock_iff d a _).2 (by simpa using hX), rfl⟩
  · rw [← sub_eq_zero, ← neg_eq_zero, ← h0]; noncomm_ring
  · rw [← sub_eq_zero, ← neg_eq_zero, ← h0]; noncomm_ring
end GlobalTheory.CuspCharCheck
