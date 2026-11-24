-- Prove2me | solution 1 for GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:04:14.531952+00:00
-- url     : https://prove2.me/submissions/3b8bb5f0-115a-48a8-8b4b-228d8905217d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardNonregularResiduesModPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardNonregularResiduesModPowSubOneLeStatement
import Theorems.Thm_GlobalTheory_CuspGL_card_nonregular_residues_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ q n : ℕ, 2 ≤ q → 0 < n → ((Finset.Ioo 0 (q ^ n - 1)).filter (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])).card ≤ ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) := by
  first | exact @GlobalTheory.CuspGL.card_nonregular_residues_le | exact GlobalTheory.CuspGL.card_nonregular_residues_le | (intros; apply GlobalTheory.CuspGL.card_nonregular_residues_le <;> assumption)
end _root_.GlobalTheory.T
