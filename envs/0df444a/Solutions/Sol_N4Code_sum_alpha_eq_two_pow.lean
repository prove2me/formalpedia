-- Prove2me | solution 1 for N4Code.sum_alpha_eq_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:18.685467+00:00
-- url     : https://prove2.me/submissions/d81f973d-ab44-4b72-8b8b-2dba4367d6e5

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
import Theorems.Thm_N4Code_dCode_le

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) : (∑ d ∈ Finset.Icc 0 n, alpha C d) = 2 ^ n := by
  rw [show (∑ d ∈ Finset.Icc 0 n, alpha C d) =
        ∑ d ∈ Finset.Icc 0 n, ∑ y ∈ (Finset.univ : Finset (Word n)),
          if dCode C y = d then 1 else 0 by
        apply Finset.sum_congr rfl
        intro d _
        rfl]
  rw [Finset.sum_comm]
  have hbool : Fintype.card Bool = 2 := by decide
  simp [Finset.sum_ite_eq, dCode_le, Fintype.card_pi, hbool]
end N4Code
