-- Prove2me | solution 1 for GeneralPieces.Ring.opWin_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:38:57.179043+00:00
-- url     : https://prove2.me/submissions/dba84da1-5cca-4407-bfce-8d86ba779714

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_nabla_sum
import Theorems.Thm_P2M_GeneralPieces_Ring_sum_win__8dc8cdd1a805
import Theorems.Thm_P2M_GeneralPieces_Ring_sum_tup_succ__ab6e7a7dfbc1
import Theorems.Thm_GeneralPieces_Ring_term_cons_neg
import Theorems.Thm_GeneralPieces_Ring_term_cons_pos

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (n : ℕ+) (μ : List ℕ+) (M : ℕ) (r : ℤ) (f : V) : opWin (n :: μ) M r f =
    ∑ l ∈ Icc 1 M, (binom ((l : ℤ) - 1) ((n : ℤ) - 1) : ℚ) • nabla (-(l : ℤ)) (opWin μ M (r - l) f) +
      ∑ k ∈ Icc 1 M, (binom (-(k : ℤ) - 1) ((n : ℤ) - 1) : ℚ) • opWin μ M (r + k) (nabla k f) := by
  unfold opWin
  rw [sum_filter, List.length_cons, sum_tup_succ', sum_win']
  congr 1
  · refine sum_congr rfl fun l hl => ?_
    have hl1 := (mem_Icc.1 hl).1
    rw [nabla_sum, smul_sum, sum_filter]
    refine sum_congr rfl fun ks _ => ?_
    have hc : (-(l : ℤ) :: ks).sum = -r ↔ ks.sum = -(r - l) := by
      rw [List.sum_cons]; constructor <;> intro h <;> omega
    rw [if_congr hc rfl rfl, term_cons_neg n μ (by omega), neg_neg]
  · refine sum_congr rfl fun k hk => ?_
    have hk1 := (mem_Icc.1 hk).1
    rw [smul_sum, sum_filter]
    refine sum_congr rfl fun ks _ => ?_
    have hc : ((k : ℤ) :: ks).sum = -r ↔ ks.sum = -(r + k) := by
      rw [List.sum_cons]; constructor <;> intro h <;> omega
    rw [if_congr hc rfl rfl, term_cons_pos n μ (by omega)]
end GeneralPieces.Ring
