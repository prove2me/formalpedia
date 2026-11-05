-- Prove2me | solution 1 for GeneralPieces.Sizes.coef_opMon_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:29:01.14947+00:00
-- url     : https://prove2.me/submissions/cbc0cf77-89f5-4ad0-b047-421af5ad47be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_bet_eq
import Theorems.Thm_GeneralPieces_Sizes_toFinset_toN
import Theorems.Thm_GeneralPieces_Ring_count_toN
import Theorems.Thm_GeneralPieces_Ring_mem_toN
import Theorems.Thm_GeneralPieces_Ring_toN_erase
import Theorems.Thm_GeneralPieces_stBridge


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (n : ℕ+) (a' : List ℕ+) (r : ℤ) (σ' σ : Ptn) :
    coef σ' (opMon (n :: a') r (tpow σ)) =
      ∑ l ∈ σ'.toFinset, ((binom (((l : ℕ) : ℤ) - 1) ((n : ℤ) - 1) : ℤ) : ℚ) * coef (σ'.erase l) (opMon a' (r - (l : ℕ)) (tpow σ)) +
        ∑ k ∈ σ.toFinset, ((binom (-((k : ℕ) : ℤ) - 1) ((n : ℤ) - 1) * ((k : ℕ) * σ.count k) : ℤ) : ℚ) *
          coef σ' (opMon a' (r + (k : ℕ)) (tpow (σ.erase k))) := by
  have e : toL (n :: a') = (n : ℕ) :: toL a' := rfl
  rw [stBridge, e, ClauseBound.Boson.op, ClauseBound.Boson.nop, toFinset_toN, toFinset_toN, sum_image PNat.coe_injective.injOn,
    sum_image PNat.coe_injective.injOn]
  push_cast
  congr 1
  · refine sum_congr rfl fun l hl => ?_
    have hl0 : ((l : ℕ) : ℤ) ≠ 0 := by have := l.pos; omega
    rw [ClauseBound.Boson.cre, if_pos ((mem_toN _ _).2 (Multiset.mem_toFinset.1 hl)), ← toN_erase, stBridge, bet_eq n hl0]
  · refine sum_congr rfl fun k _ => ?_
    have hk0 : -((k : ℕ) : ℤ) ≠ 0 := by have := k.pos; omega
    rw [ClauseBound.Boson.ann, count_toN, ← toN_erase, stBridge, bet_eq n hk0]
    push_cast
    ring
end GeneralPieces.Sizes
