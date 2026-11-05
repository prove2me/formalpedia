-- Prove2me | solution 1 for Groundwork.Prog.NetE.natAbs_le_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:59:21.91232+00:00
-- url     : https://prove2.me/submissions/92d808a6-cdd5-442f-8b7b-afe3503f59a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun

set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution {z : ℤ} {n : ℕ} (h : |z| ≤ (n : ℤ)) : z.natAbs ≤ n := by
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h
end Groundwork.Prog.NetE
