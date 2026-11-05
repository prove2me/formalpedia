-- Prove2me | solution 1 for Groundwork.Host.look_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:52:39.788807+00:00
-- url     : https://prove2.me/submissions/23e870f0-3e47-403f-a96d-9804ea2e25ba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_dupF_within


set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host
variable {M : Stepped (List Bool) Bool}
variable [Enc M.σ]
variable {Ps Po : Fr} {tS tO : ℕ → ℕ}
  (hS : ∀ (s : M.σ) (M' A B N : List Sym),
    Ps.Within (st (wd s ++ M') A B N) (tS (len s)) (st (wd (M.step s) ++ M') A B N))
  (hO : ∀ (s : M.σ) (M' A B N : List Sym),
    Po.Within (st (wd s ++ M') A B N) (tO (len s)) (st (wd (M.out s) ++ M') A B N))
include hO
namespace Groundwork.Host
theorem _root_.solution (s : M.σ) (M' A B N : List Sym) : (look Po).Within (st (wd s ++ M') A B N)
    (3 * len s + 3 + tO (len s)) (st (wd (M.out s) ++ (wd s ++ M')) A B N) :=
  (dupF_within (Enc.toV s) M' A B N).seq (hO s _ A B N)
end Groundwork.Host
