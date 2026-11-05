-- Prove2me | solution 1 for Groundwork.Prog.Evaluator.Correct.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:24:45.715749+00:00
-- url     : https://prove2.me/submissions/aff51fe7-3d86-4e8d-85cd-d1fd1d57cec7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_BruteE

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset Stepped
namespace Groundwork.Prog
namespace Evaluator.Correct
theorem _root_.solution {E : Evaluator} {K : ℕ} {ε ε' : ℝ} (h : E.Correct K ε) (hε : ε ≤ ε') :
    E.Correct K ε' := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun C _ lam R c B t S Rm hl ht hR => ?_⟩
  obtain ⟨T, h1, h2⟩ := hA C lam R c B t S Rm hl ht hR
  refine ⟨T, h1, h2.trans ?_⟩
  have : (2 : ℝ) ^ (ε * (K : ℝ) ^ 2 * lam c) ≤ (2 : ℝ) ^ (ε' * (K : ℝ) ^ 2 * lam c) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by gcongr)
  gcongr
end Evaluator.Correct
end Groundwork.Prog
