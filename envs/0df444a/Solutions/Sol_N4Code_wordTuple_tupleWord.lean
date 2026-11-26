-- Prove2me | solution 1 for N4Code.wordTuple_tupleWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:05.102982+00:00
-- url     : https://prove2.me/submissions/9c0ed9db-429d-4bfa-9f51-915e9d381b20

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
import Theorems.Thm_N4Code_fin16_val_mem_Icc
import Theorems.Thm_N4Code_onesOn_tupleWord

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (k : ℕ → ℕ)
    {g : Fin 16 → Finset (Fin n)} (hg : GoodTuplePred C k g) :
    wordTuple C (tupleWord C g) = g := by
  funext a
  change onesOn (fiber C a.val) (tupleWord C g) = g a
  rw [onesOn_tupleWord C k g hg (fin16_val_mem_Icc a)]
end N4Code
