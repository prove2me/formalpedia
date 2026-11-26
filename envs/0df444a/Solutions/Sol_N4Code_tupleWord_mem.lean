-- Prove2me | solution 1 for N4Code.tupleWord_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:02.214658+00:00
-- url     : https://prove2.me/submissions/bd7c3204-f35e-479d-867b-b93eb456f162

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic
import Theorems.Thm_N4Code_w_i_eq_card_onesOn
import Theorems.Thm_N4Code_goodWord_iff
import Theorems.Thm_N4Code_onesOn_tupleWord

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (k : ℕ → ℕ) {g : Fin 16 → Finset (Fin n)}
    (hg : GoodTuplePred C k g) : tupleWord C g ∈ GoodWords C k := by
  apply (goodWord_iff C k (tupleWord C g)).2
  intro i hi
  have hi' : i < 16 := by
    have hi'' : i ≤ 15 := (Finset.mem_Icc.mp hi).2
    omega
  rw [w_i_eq_card_onesOn, onesOn_tupleWord C k g hg hi]
  exact (Finset.mem_powersetCard.mp (hg ⟨i, hi'⟩)).2
end N4Code
