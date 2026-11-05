-- Prove2me | solution 1 for Groundwork.Prog.sum_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:55:31.068632+00:00
-- url     : https://prove2.me/submissions/0415e381-7204-4d0f-89cf-30f5e5e74928

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Math_GridArith
import Definitions.Def_StepMachines_Prog_GridDefs

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
namespace Groundwork.Prog
theorem _root_.solution (n R : ℕ) (F : (Fin R → ℕ) → ℤ) :
    ∑ y ∈ range ((n + 1) ^ R), F (fun q => digit n y q) = ∑ ι ∈ Fintype.piFinset fun _ : Fin R => range (n + 1), F ι := by
  rw [Finset.sum_range fun y => F fun q : Fin R => digit n y q,
    ← (finFunctionFinEquiv (m := n + 1) (n := R)).sum_comp]
  refine Finset.sum_bij' (fun f _ q => (f q).val)
    (fun ι hι q => ⟨ι q, Finset.mem_range.1 (Fintype.mem_piFinset.1 hι q)⟩) ?_ ?_ ?_ ?_ ?_
  · exact fun f _ => Fintype.mem_piFinset.2 fun q => Finset.mem_range.2 (f q).2
  · exact fun _ _ => Finset.mem_univ _
  · exact fun _ _ => rfl
  · exact fun _ _ => rfl
  · intro f _
    congr 1
    funext q
    have := congrFun (finFunctionFinEquiv.symm_apply_apply f) q
    rw [← this]
    rfl
end Groundwork.Prog
