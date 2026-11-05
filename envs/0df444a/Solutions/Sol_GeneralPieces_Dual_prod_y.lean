-- Prove2me | solution 1 for GeneralPieces.Dual.prod_y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:18:51.506746+00:00
-- url     : https://prove2.me/submissions/e1306bf3-00a0-4ee3-8cc4-aca5e08fccaf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_mem_tuples
import Theorems.Thm_GeneralPieces_Dual_prod_map_sum
import Theorems.Thm_GeneralPieces_Dual_prod_zip_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : List ℕ+) : (μ.map y).prod = ∑ js ∈ tuples (μ.map fun n : ℕ+ => Icc 1 (n : ℕ)),
    (List.zipWith (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ)) μ js).prod • tpow ((js.map Nat.toPNat' : List ℕ+) : Multiset ℕ+) := by
  have h := prod_map_sum μ (fun n : ℕ+ => Icc 1 (n : ℕ)) (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ) • (X j.toPNat' : V))
  have h0 : (μ.map y) = μ.map fun n : ℕ+ => ∑ j ∈ Icc 1 (n : ℕ), ((n : ℕ).choose j : ℚ) • (X j.toPNat' : V) := rfl
  rw [h0, h]
  refine sum_congr rfl fun js hjs => ?_
  have hl : js.length = μ.length := by
    have := ((mem_tuples _ _).1 hjs).length_eq
    simpa using this
  exact prod_zip_smul _ _ μ js hl
end GeneralPieces.Dual
