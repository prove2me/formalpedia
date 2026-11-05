-- Prove2me | solution 1 for GeneralPieces.Dual.nabla_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:23:07.54236+00:00
-- url     : https://prove2.me/submissions/f62f5196-9c02-4f5c-99c6-ab9152cf72b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_pn_coe
import Theorems.Thm_GeneralPieces_Ring_pn_coe


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (n : ℕ+) (ν : Ptn) : nabla (n : ℤ) (tpow ν) = (((n : ℕ) : ℚ) * (ν.count n : ℚ)) • tpow (ν.erase n) := by
  have hpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast n.pos
  have e : Multiset.toFinsupp ν - Finsupp.single n 1 = Multiset.toFinsupp (ν.erase n) := by
    ext a
    rw [Finsupp.tsub_apply, Multiset.toFinsupp_apply, Multiset.toFinsupp_apply, Finsupp.single_apply]
    by_cases h : n = a
    · subst h; simp
    · rw [if_neg h, Multiset.count_erase_of_ne (Ne.symm h)]; simp
  rw [nabla, if_neg (by omega), if_pos hpos, pn_coe, tpow, pderiv_monomial, e, tpow, smul_monomial, smul_monomial, Multiset.toFinsupp_apply]
  congr 1
  simp
end GeneralPieces.Dual
