-- Prove2me | solution 1 for Groundwork.Stepped.exists_round_of_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:25:19.207261+00:00
-- url     : https://prove2.me/submissions/5c38b870-d5a5-4937-8602-1cb0fdc71146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
import Theorems.Thm_Groundwork_Stepped_Orbit_forall
import Theorems.Thm_Groundwork_Stepped_round_fst

set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}
variable (step : ν → Option (ν × ν))
namespace Groundwork.Stepped
theorem _root_.solution {s : ν} {xs : List (List ν)} (h : Orbit (walkNext step) (some [s]) xs) :
    ∀ y ∈ xs, ∃ i, ((Sparsify.round step)^[i] ([s], [])).1 = y := by
  refine h.forall _ (fun x hx => ⟨0, Option.some.inj hx⟩) ?_
  rintro y z ⟨i, hi⟩ hz
  refine ⟨i + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  generalize (Sparsify.round step)^[i] ([s], []) = p at hi
  obtain ⟨st, out⟩ := p
  subst hi
  exact round_fst step hz out
end Groundwork.Stepped
