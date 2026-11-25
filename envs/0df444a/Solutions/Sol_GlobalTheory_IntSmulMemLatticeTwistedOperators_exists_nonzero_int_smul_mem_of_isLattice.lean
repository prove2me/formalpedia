-- Prove2me | solution 1 for GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:55:59.341272+00:00
-- url     : https://prove2.me/submissions/5d2408a8-4f68-4713-b179-cbc54571787e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsNonzeroIntSmulMemOfIsLattice
import Theorems.Thm_GlobalTheory_IntSmulMemLatticeTwistedOperators_exists_int_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntSmulMemLatticeTwistedOperators
open NumberField
namespace GlobalTheory.IntSmulMemLatticeTwistedOperators
theorem _root_.solution : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : Fin n → E), ∃ (c : ℤ), c ≠ (0 : ℤ) ∧ c • v ∈ L :=
  fun L hL v => exists_int_smul_mem L hL v
end GlobalTheory.IntSmulMemLatticeTwistedOperators
