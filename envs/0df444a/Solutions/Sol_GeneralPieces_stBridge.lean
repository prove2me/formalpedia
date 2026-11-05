-- Prove2me | solution 1 for GeneralPieces.stBridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:31:48.901205+00:00
-- url     : https://prove2.me/submissions/f07c11ab-ffc3-4cfd-a77e-e7b7cacdce69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_term_eq
import Theorems.Thm_GeneralPieces_Ring_zero_notMem_toN
import Theorems.Thm_GeneralPieces_Ring_sum_toN
import Theorems.Thm_GeneralPieces_Ring_coef_nordQ
import Theorems.Thm_GeneralPieces_Ring_wtQ_eq
import Theorems.Thm_GeneralPieces_Ring_opMon_eq_sum
import Theorems.Thm_ClauseBound_Boson_Text_mem_tup
import Theorems.Thm_ClauseBound_Boson_op_eq_sum


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces
theorem _root_.solution : StBridge := by
  intro a r π σ
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = wt σ + r.natAbs + wt π := ⟨_, rfl⟩
  have hlen : (toL a).length = a.length := List.length_map _
  rw [opMon_eq_sum a r σ M (by rw [Int.abs_eq_natAbs]; omega),
    ClauseBound.Boson.op_eq_sum (toL a) r (toN π) (toN σ) M (zero_notMem_toN π) (zero_notMem_toN σ) (by rw [sum_toN]; omega) (by rw [sum_toN]; omega), hlen]
  unfold coef
  rw [coeff_sum]
  push_cast
  refine sum_congr rfl fun ks hks => ?_
  have h0 : ∀ k ∈ ks, k ≠ 0 := fun k hk => ((ClauseBound.Boson.Text.mem_tup.1 (mem_filter.1 hks).1).2 k hk).1
  have := coef_nordQ ks h0 π σ
  unfold coef at this
  rw [term_eq, coeff_smul, smul_eq_mul, this, wtQ_eq]
end GeneralPieces
