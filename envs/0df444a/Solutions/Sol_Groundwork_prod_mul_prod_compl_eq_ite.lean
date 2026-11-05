-- Prove2me | solution 1 for Groundwork.prod_mul_prod_compl_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:08:05.794421+00:00
-- url     : https://prove2.me/submissions/d2347f45-91a9-4f46-ba08-b3793b5a7ba0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {n : ℕ} (S : Finset (Fin n)) (g1 g0 : Fin n → ℤ) :
    (∏ k ∈ S, g1 k) * ∏ k ∈ Sᶜ, g0 k = ∏ k, if k ∈ S then g1 k else g0 k := by
  rw [← prod_mul_prod_compl S]
  congr 1
  · exact prod_congr rfl fun k hk => by rw [if_pos hk]
  · exact prod_congr rfl fun k hk => by rw [if_neg (mem_compl.1 hk)]
end Groundwork
