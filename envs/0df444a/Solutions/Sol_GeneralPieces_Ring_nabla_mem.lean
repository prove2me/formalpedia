-- Prove2me | solution 1 for GeneralPieces.Ring.nabla_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:23:23.501631+00:00
-- url     : https://prove2.me/submissions/13128167-f0cb-43f2-a0f0-44956ad11e27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_GeneralPieces_Ring_weight_toFinsupp
import Theorems.Thm_GeneralPieces_Ring_VE_neg
import Theorems.Thm_GeneralPieces_Ring_mem_VE_natCast
import Theorems.Thm_GeneralPieces_Ring_mem_VE_iff
import Theorems.Thm_GeneralPieces_Ring_nabla_neg
import Theorems.Thm_GeneralPieces_Ring_nabla_pos
import Theorems.Thm_GeneralPieces_Ring_nabla_zero_right
import Theorems.Thm_GeneralPieces_Ring_pn_coe


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {k E : ℤ} {f : V} (hk : k ≠ 0) (hf : f ∈ VE E) : nabla k f ∈ VE (E - k) := by
  by_cases hE : 0 ≤ E
  · obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hE
    have hf' := (mem_VE_natCast e f).1 hf
    have hp := pn_coe hk
    rcases lt_or_gt_of_ne hk with hk' | hk'
    · have e1 : (e : ℤ) - k = ((wgt (pn k) + e : ℕ) : ℤ) := by unfold wgt; push_cast; omega
      rw [nabla_neg hk', e1, mem_VE_natCast]
      exact (isWeightedHomogeneous_X ℚ wgt (pn k)).mul hf'
    · rw [nabla_pos hk']
      refine Submodule.smul_mem _ _ ((mem_VE_iff _ _).2 fun μ hμ => ?_)
      unfold coef at hμ
      rw [coeff_pderiv] at hμ
      have h1 := hf' (left_ne_zero_of_mul hμ)
      rw [map_add, weight_toFinsupp, Finsupp.weight_single] at h1
      simp only [wgt, smul_eq_mul, one_mul] at h1
      omega
  · rw [VE_neg (by omega), Submodule.mem_bot] at hf
    rw [hf, nabla_zero_right]
    exact Submodule.zero_mem _
end GeneralPieces.Ring
