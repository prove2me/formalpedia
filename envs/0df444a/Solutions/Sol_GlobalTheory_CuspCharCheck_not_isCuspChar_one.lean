-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.not_isCuspChar_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:39:04.702212+00:00
-- url     : https://prove2.me/submissions/196044f3-ee3a-4da3-bbf7-35490f642c55

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
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) : ¬ IsCuspChar (fun _ : GL (Fin d) F => (1 : ℂ)) := by
  classical
  rintro ⟨-, h⟩
  have h1 := h 1 one_pos (by omega)
  rw [Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
  exact h1 (Finset.mem_univ 1) (unipSubgroup d 1 : Subgroup (GL (Fin d) F)).one_mem
end GlobalTheory.CuspCharCheck
