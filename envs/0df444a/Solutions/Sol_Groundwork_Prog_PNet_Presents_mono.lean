-- Prove2me | solution 1 for Groundwork.Prog.PNet.Presents.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:25:54.863621+00:00
-- url     : https://prove2.me/submissions/854539dd-6104-4743-b921-c0a90b4c138c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Math_GridArith
import Definitions.Def_StepMachines_Prog_GridDefs
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
namespace Groundwork.Prog
namespace PNet.Presents
theorem _root_.solution {C : Type} {Np : PNet C} {c : C} {g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)}
    {t t' S S' : ℕ} (h : Np.Presents c N t S) (ht : t ≤ t') (hS : S ≤ S') : Np.Presents c N t' S' :=
  ⟨h.S_eq, h.c_eq, h.lab_eq, fun a z hz => (h.W_runs a z hz).mono ht hS,
    fun a b z θ hab hz hθ => (h.f_runs a b z θ hab hz hθ).mono ht hS⟩
end PNet.Presents
end Groundwork.Prog
