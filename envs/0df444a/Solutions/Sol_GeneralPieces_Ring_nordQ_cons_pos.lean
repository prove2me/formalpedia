-- Prove2me | solution 1 for GeneralPieces.Ring.nordQ_cons_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:26:40.302026+00:00
-- url     : https://prove2.me/submissions/3ee3fbb7-1888-47e8-b195-c0fc3e095e61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_nabla_foldr_pos

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {k : ℤ} (hk : 0 < k) (ks : List ℤ) (f : V) : nordQ (k :: ks) f = nordQ ks (nabla k f) := by
  have e1 : (k :: ks).filter (· < 0) = ks.filter (· < 0) := List.filter_cons_of_neg (by simp; omega)
  have e2 : (k :: ks).filter (0 < ·) = k :: ks.filter (0 < ·) := List.filter_cons_of_pos (by simpa using hk)
  unfold nordQ
  rw [e1, e2, List.foldr_cons, nabla_foldr_pos hk _ fun x hx => by simpa using (List.mem_filter.1 hx).2]
end GeneralPieces.Ring
