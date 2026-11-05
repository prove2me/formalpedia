-- Prove2me | solution 1 for GeneralPieces.Ring.nordQ_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:37:48.682536+00:00
-- url     : https://prove2.me/submissions/841a9b2f-9a04-4073-9058-b48ba8bded91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_nabla_comm_pos
import Theorems.Thm_GeneralPieces_Ring_nabla_neg


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {ks ks' : List ℤ} (h : ks.Perm ks') (f : V) : nordQ ks f = nordQ ks' f := by
  unfold nordQ
  rw [(h.filter (0 < ·)).foldr_eq' (f := nabla) (fun x hx y hy z => nabla_comm_pos (by simpa using (List.mem_filter.1 hy).2) (by simpa using (List.mem_filter.1 hx).2) z) f,
    (h.filter (· < 0)).foldr_eq' (f := nabla) (fun x hx y hy z => by
      rw [nabla_neg (by simpa using (List.mem_filter.1 hy).2), nabla_neg (by simpa using (List.mem_filter.1 hx).2),
        nabla_neg (by simpa using (List.mem_filter.1 hx).2), nabla_neg (by simpa using (List.mem_filter.1 hy).2), mul_left_comm]) _]
end GeneralPieces.Ring
