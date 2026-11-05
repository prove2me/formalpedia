-- Prove2me | solution 1 for Groundwork.sum_toWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:38.971883+00:00
-- url     : https://prove2.me/submissions/6af481a2-1ebc-4a6f-ae5c-04f33774a6d3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_StepMachines_Prog_Chunks
import Theorems.Thm_Groundwork_toWord_injOn

set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {X : Type*} [AddCommMonoid X] (ℓ : ℕ) (G : List Bool → X) :
    ∑ y ∈ range (2 ^ ℓ), G (toWord ℓ y) = ∑ w ∈ words ℓ, G w :=
  (sum_image (toWord_injOn ℓ)).symm
end Groundwork
