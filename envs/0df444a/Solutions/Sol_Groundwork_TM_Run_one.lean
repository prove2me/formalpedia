-- Prove2me | solution 1 for Groundwork.TM.Run.one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:19:08.39881+00:00
-- url     : https://prove2.me/submissions/36a168c2-e0f5-4893-8a85-7b35b8957f22

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
theorem _root_.solution {C : Type} {f : C → Option C} {a b : C} (h : f a = some b) : Run f a 1 b := ⟨b, h, rfl⟩
end Run
end Groundwork.TM
