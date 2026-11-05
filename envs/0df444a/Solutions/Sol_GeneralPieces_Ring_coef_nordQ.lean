-- Prove2me | solution 1 for GeneralPieces.Ring.coef_nordQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:27:47.862182+00:00
-- url     : https://prove2.me/submissions/f7d94757-f8aa-46f3-93b2-184c6d1cb483

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_pn_coe
import Theorems.Thm_GeneralPieces_Ring_coef_X_mul
import Theorems.Thm_GeneralPieces_Ring_nabla_pos_tpow
import Theorems.Thm_GeneralPieces_Ring_coef_tpow
import Theorems.Thm_GeneralPieces_Ring_coef_smul
import Theorems.Thm_GeneralPieces_Ring_nordQ_nil
import Theorems.Thm_GeneralPieces_Ring_nordQ_cons_neg
import Theorems.Thm_GeneralPieces_Ring_nordQ_cons_pos
import Theorems.Thm_GeneralPieces_Ring_nordQ_smul
import Theorems.Thm_GeneralPieces_Ring_toN_injective
import Theorems.Thm_GeneralPieces_Ring_toN_erase
import Theorems.Thm_GeneralPieces_Ring_mem_toN
import Theorems.Thm_GeneralPieces_Ring_count_toN
import Theorems.Thm_ClauseBound_Boson_Text_coef_X_mul
import Theorems.Thm_ClauseBound_Boson_Text_coef_mon
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_ClauseBound_Boson_Text_nabPos_mon
import Theorems.Thm_ClauseBound_Boson_Text_nord_cons_neg
import Theorems.Thm_ClauseBound_Boson_Text_nord_cons_pos
import Theorems.Thm_ClauseBound_Boson_Text_nord_nil
import Theorems.Thm_ClauseBound_Boson_Text_nord_smul


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (ks : List ℤ) : (∀ k ∈ ks, k ≠ 0) → ∀ π σ : Ptn,
    coef π (nordQ ks (tpow σ)) = ((ClauseBound.Boson.coef (toN π) (ClauseBound.Boson.nord ks (ClauseBound.Boson.mon (toN σ))) : ℤ) : ℚ) := by
  induction ks with
  | nil =>
    intro _ π σ
    rw [nordQ_nil, coef_tpow, ClauseBound.Boson.Text.nord_nil, ClauseBound.Boson.Text.coef_mon]
    by_cases h : π = σ
    · simp [h]
    · rw [if_neg h, if_neg fun h' => h (toN_injective h')]
      simp
  | cons k ks ih =>
    intro h0 π σ
    have hk0 : k ≠ 0 := h0 k (by simp)
    have ih' := ih fun x hx => h0 x (by simp [hx])
    rcases lt_or_gt_of_ne hk0 with hk | hk
    · have e : (-k).toNat = ((pn k : ℕ+) : ℕ) := by rw [pn_coe hk0]; omega
      rw [nordQ_cons_neg hk, coef_X_mul, ClauseBound.Boson.Text.nord_cons_neg hk, ClauseBound.Boson.Text.coef_X_mul, e]
      by_cases hm : pn k ∈ π
      · rw [if_pos hm, if_pos ((mem_toN π _).2 hm), ih', toN_erase]
      · rw [if_neg hm, if_neg fun h => hm ((mem_toN π _).1 h)]
        simp
    · have e : k = (((pn k : ℕ+) : ℕ) : ℤ) := by rw [pn_coe hk0]; omega
      rw [nordQ_cons_pos hk, nabla_pos_tpow hk, nordQ_smul, coef_smul, ih', ClauseBound.Boson.Text.nord_cons_pos hk]
      conv_rhs => rw [e, ClauseBound.Boson.Text.nabPos_mon, ClauseBound.Boson.Text.nord_smul, ClauseBound.Boson.Text.coef_smul, count_toN, ← toN_erase, ← e]
      push_cast
      ring
end GeneralPieces.Ring
