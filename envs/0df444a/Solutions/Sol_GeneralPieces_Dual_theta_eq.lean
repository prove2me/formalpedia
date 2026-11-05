-- Prove2me | solution 1 for GeneralPieces.Dual.theta_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:26:22.25987+00:00
-- url     : https://prove2.me/submissions/7c0c5c1e-4ed4-4136-9436-d12d697daca3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_binomRules


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (n : ℕ+) (k : ℤ) : theta n k = binom ((n : ℤ) - k - 1) ((n : ℤ) - 1) := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (n : ℕ) = p + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  have h := binomRules.vandermonde (n : ℤ) (-k - 1) p
  have hn : ((n : ℕ) : ℤ) = (p : ℤ) + 1 := by exact_mod_cast hp
  have hI : Icc 1 (n : ℕ) = Ico (0 + 1) (p + 1 + 1) := by ext j; simp only [mem_Icc, mem_Ico]; omega
  rw [theta, hI, ← sum_Ico_add' _ 0 (p + 1) 1, ← range_eq_Ico]
  rw [show (n : ℤ) - k - 1 = (n : ℤ) + (-k - 1) by ring, show ((n : ℕ) : ℤ) - 1 = (p : ℤ) by omega, ← h]
  refine sum_congr rfl fun j _ => ?_
  congr 2 <;> push_cast <;> omega
end GeneralPieces.Dual
