-- Prove2me | solution 1 for Groundwork.TM.Run.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:16:56.912869+00:00
-- url     : https://prove2.me/submissions/e39ebc1b-5e13-4f61-97fc-cc2b76f3a859

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ToTuring_TM_Run

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
namespace Groundwork.TM
namespace Run
theorem _root_.solution {C : Type} {f : C → Option C} : ∀ {m : ℕ} {a b c : C} {n : ℕ}, Run f a m b → Run f b n c → Run f a (m + n) c
  | 0, _, _, _, n, h, h' => by cases h; simpa using h'
  | m + 1, _, _, _, n, ⟨d, hd, h⟩, h' => by
    rw [Nat.add_right_comm]
    exact ⟨d, hd, solution h h'⟩
end Run
end Groundwork.TM
