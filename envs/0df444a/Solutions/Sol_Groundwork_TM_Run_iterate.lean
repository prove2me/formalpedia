-- Prove2me | solution 1 for Groundwork.TM.Run.iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:02:32.92496+00:00
-- url     : https://prove2.me/submissions/001dfafd-851f-415f-ac91-1e029d8b8c79

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
theorem _root_.solution {C : Type} {f : C → Option C} : ∀ {n : ℕ} {a b : C}, Run f a n b → (flip bind f)^[n] (some a) = some b
  | 0, _, _, h => by cases h; rfl
  | n + 1, a, b, ⟨c, hc, h⟩ => by
    rw [Function.iterate_succ_apply]
    have : flip bind f (some a) = some c := hc
    rw [this]; exact solution h
end Run
end Groundwork.TM
