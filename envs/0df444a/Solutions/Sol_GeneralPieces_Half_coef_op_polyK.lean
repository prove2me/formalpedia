-- Prove2me | solution 1 for GeneralPieces.Half.coef_op_polyK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:44:08.524207+00:00
-- url     : https://prove2.me/submissions/f3fad79a-6905-41bf-96b9-007aa0510633

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_toL_toPNats
import Theorems.Thm_GeneralPieces_Half_polyK_nil
import Theorems.Thm_GeneralPieces_Half_polyK_cons
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_smul
import Theorems.Thm_GeneralPieces_Ring_op_add_left
import Theorems.Thm_GeneralPieces_Ring_op_smul_left
import Theorems.Thm_GeneralPieces_Ring_op_tpow
import Theorems.Thm_GeneralPieces_stBridge


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution (k : ℤ × List ℕ → ℚ) {A : ClauseBound.Boson.FA} (hA : ∀ c ∈ A, ClauseBound.Boson.Pos c.2) (r : ℤ) (π σ : Ptn) :
    coef π (op (polyK k A) r (tpow σ)) = (A.map fun c => k c * ((ClauseBound.Boson.op c.2 r (toN π) (toN σ) : ℤ) : ℚ)).sum := by
  induction A with
  | nil =>
    have h : op (0 : V) r (tpow σ) = 0 := map_zero (opLeft r (tpow σ))
    rw [polyK_nil, h]
    simp [coef]
  | cons c A ih =>
    have h2 : op (tpow (ptn c.2)) r (tpow σ) = opMon (toPNats c.2) r (tpow σ) := op_tpow (toPNats c.2) r (tpow σ)
    have h3 : ∀ f g : V, coef π (f + g) = coef π f + coef π g := fun f g => coeff_add _ f g
    rw [polyK_cons, op_add_left, h3, op_smul_left, coef_smul, h2, stBridge, toL_toPNats (hA c List.mem_cons_self), List.map_cons, List.sum_cons,
      ih fun c' hc' => hA c' (List.mem_cons_of_mem _ hc')]
end GeneralPieces.Half
