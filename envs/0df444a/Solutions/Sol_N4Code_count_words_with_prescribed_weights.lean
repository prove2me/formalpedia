-- Prove2me | solution 1 for N4Code.count_words_with_prescribed_weights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:44.298124+00:00
-- url     : https://prove2.me/submissions/a75220cf-7a52-4a4b-9620-1ad239db2161

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
import Theorems.Thm_N4Code_goodWords_card
import Theorems.Thm_N4Code_goodTuples_card

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (k : ℕ → ℕ) :
    ((Finset.univ : Finset (Word n)).filter
        fun y : Word n => (∑ i ∈ Finset.Icc 0 15, if w_i C i y = k i then 0 else 1) = 0).card =
      ∏ i ∈ Finset.Icc 0 15, Nat.choose (count C i) (k i) := by
  rw [show ((Finset.univ : Finset (Word n)).filter
        fun y : Word n => (∑ i ∈ Finset.Icc 0 15, if w_i C i y = k i then 0 else 1) = 0) =
      GoodWords C k by
    rfl]
  rw [goodWords_card, goodTuples_card]
end N4Code
