-- Prove2me | solution 1 for Groundwork.Prog.sized_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:31:35.183199+00:00
-- url     : https://prove2.me/submissions/8249624e-c82b-4a74-84a7-3431fd3f6c99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatArith
import Definitions.Def_StepMachines_Prog_Count

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset Groundwork.Prog.Count
namespace Groundwork.Prog
theorem _root_.solution {J σ τ : Type} [Fintype J] [LinearOrder J] {N : Network J σ τ} {P P' B : ℕ} (h : N.Sized P B)
    (hP : P ≤ P') : N.Sized P' B :=
  { h with
    card_S := fun a => (h.card_S a).trans (Nat.pow_le_pow_right (by norm_num) hP)
    sum_c := fun a => (h.sum_c a).trans hP }
end Groundwork.Prog
