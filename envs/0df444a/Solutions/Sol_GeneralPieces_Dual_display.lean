-- Prove2me | solution 1 for GeneralPieces.Dual.display
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:20:20.528387+00:00
-- url     : https://prove2.me/submissions/598e6507-27fc-48e5-93a1-6225c9b18e82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_mem_tuples
import Theorems.Thm_GeneralPieces_Dual_mem_posTuples
import Theorems.Thm_GeneralPieces_Dual_term_pos
import Theorems.Thm_GeneralPieces_Dual_opMon_eq_sum
import Theorems.Thm_GeneralPieces_Dual_prod_y
import Theorems.Thm_GeneralPieces_Dual_op_sum
import Theorems.Thm_GeneralPieces_Dual_sum_coeff
import Theorems.Thm_GeneralPieces_Ring_Bd_mono
import Theorems.Thm_GeneralPieces_Ring_opMon_eq_sum
import Theorems.Thm_GeneralPieces_opFacts


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (h : ℕ) (μ : List ℕ+) (b : V) (hb : b ∈ VE h) :
    op (μ.map y).prod (-(h : ℤ)) b = ∑ ks ∈ posTuples μ.length h, (((List.zipWith theta μ ks).prod : ℤ) : ℚ) • nablas ks b := by
  rw [prod_y, op_sum]
  have h1 : ∀ js ∈ tuples (μ.map fun n : ℕ+ => Icc 1 (n : ℕ)),
      (List.zipWith (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ)) μ js).prod • op (tpow ((js.map Nat.toPNat' : List ℕ+) : Multiset ℕ+)) (-(h : ℤ)) b =
      ∑ ks ∈ posTuples μ.length h, ((List.zipWith (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ)) μ js).prod *
        (((List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) (js.map Nat.toPNat') ks).prod : ℤ) : ℚ)) • nablas ks b := by
    intro js hjs
    have hl : js.length = μ.length := by
      have := ((mem_tuples _ _).1 hjs).length_eq
      simpa using this
    rw [opFacts.mono, opMon_eq_sum h _ b hb, List.length_map, hl, smul_sum]
    refine sum_congr rfl fun ks hks => ?_
    rw [term_pos _ _ _ ((mem_posTuples _ _ _).1 hks).2.1, smul_smul]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun ks hks => ?_
  rw [← sum_smul, sum_coeff μ ks ((mem_posTuples _ _ _).1 hks).1]
end GeneralPieces.Dual
