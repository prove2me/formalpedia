-- Prove2me | solution 1 for Groundwork.uncross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:07:42.019053+00:00
-- url     : https://prove2.me/submissions/fa101ce9-63f6-467d-82ef-b9a46447539c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Groundwork_Cross_Bit

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution (x y u v : Bool) : X₁ x y u v = I₁ x y u v - s x y * s u v := by
  revert x y u v; decide
end Groundwork
