-- Prove2me | solution 1 for Groundwork.Prog.satP_keeps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:05:23.321144+00:00
-- url     : https://prove2.me/submissions/ddb68403-6742-4c8b-9626-04a6dd4afc3b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_ToTuring_Poly_Count
import Theorems.Thm_Groundwork_Prog_Count_wF_polyT
import Theorems.Thm_Groundwork_Prog_Count_fF_polyT
import Theorems.Thm_Groundwork_Prog_Count_capF_unary
import Theorems.Thm_Groundwork_Prog_Count_n_unary

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
namespace Groundwork.Prog
theorem _root_.solution (g k : ℕ) : (satP g k).Keeps where
  n := Count.n_unary g k
  cap := Count.capF_unary g k
  W := ⟨IsPolyT.ofFun (Count.wF_polyT g k)⟩
  f := ⟨IsPolyT.ofFun (Count.fF_polyT g k)⟩
end Groundwork.Prog
