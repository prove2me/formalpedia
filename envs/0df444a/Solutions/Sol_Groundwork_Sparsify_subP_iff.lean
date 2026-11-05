-- Prove2me | solution 1 for Groundwork.Sparsify.subP_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:11:16.914371+00:00
-- url     : https://prove2.me/submissions/e59d2918-51bb-4604-bbf6-4b8b37e6f21f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyList
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
import Definitions.Def_StepMachines_Math_SparsifyProg

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
namespace Groundwork.Sparsify
theorem _root_.solution (D C : PCl) : subP D C = true ↔ ∀ a ∈ D, a ∈ C := by simp [subP]
end Groundwork.Sparsify
