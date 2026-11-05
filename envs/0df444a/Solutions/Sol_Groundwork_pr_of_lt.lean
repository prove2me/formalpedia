-- Prove2me | solution 1 for Groundwork.pr_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:28:11.740932+00:00
-- url     : https://prove2.me/submissions/c97f4a83-8615-4d2f-92f9-95a43319eb2c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
namespace Groundwork
theorem _root_.solution [LinearOrder J] {a b : J} (h : a < b) : pr a b = (a, b) ∧ pr b a = (a, b) := by
  simp [pr, h.le]
end Groundwork
