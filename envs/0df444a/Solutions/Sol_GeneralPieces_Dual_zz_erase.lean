-- Prove2me | solution 1 for GeneralPieces.Dual.zz_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:23:08.729951+00:00
-- url     : https://prove2.me/submissions/7a26f758-f9ef-4290-b3c6-5034a66ea439

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_zz_eq_prod

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution {ν : Ptn} {n : ℕ+} (hn : n ∈ ν) : zz ν = (n : ℕ) * ν.count n * zz (ν.erase n) := by
  have hS : (ν.erase n).toFinset ⊆ ν.toFinset := fun k hk =>
    Multiset.mem_toFinset.2 (Multiset.mem_of_mem_erase (Multiset.mem_toFinset.1 hk))
  have hn' := Multiset.mem_toFinset.2 hn
  rw [zz_eq_prod hS, zz, ← mul_prod_erase _ _ hn', ← mul_prod_erase _ (fun k : ℕ+ => (k : ℕ) ^ (ν.erase n).count k * ((ν.erase n).count k).factorial) hn']
  have h1 : ∏ k ∈ ν.toFinset.erase n, (k : ℕ) ^ (ν.erase n).count k * ((ν.erase n).count k).factorial
      = ∏ k ∈ ν.toFinset.erase n, (k : ℕ) ^ ν.count k * (ν.count k).factorial :=
    prod_congr rfl fun k hk => by rw [Multiset.count_erase_of_ne (ne_of_mem_erase hk)]
  obtain ⟨c, hc⟩ : ∃ c, ν.count n = c + 1 := ⟨ν.count n - 1, by have := Multiset.count_pos.2 hn; omega⟩
  rw [h1, Multiset.count_erase_self, hc, Nat.add_sub_cancel, pow_succ, Nat.factorial_succ]
  ring
end GeneralPieces.Dual
