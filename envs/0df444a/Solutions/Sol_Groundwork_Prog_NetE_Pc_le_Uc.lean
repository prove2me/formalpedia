-- Prove2me | solution 1 for Groundwork.Prog.NetE.Pc_le_Uc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:31:38.472685+00:00
-- url     : https://prove2.me/submissions/f2476b94-639e-4cba-9f97-75c2e006ee93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_ToTuring_Poly_NetFun
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
variable {α β : Type} [Enc α] [Enc β]
variable (K g : ℕ)
variable {C : Type} [Enc C] {Np : PNet C}
variable (h : Np.Keeps)
include h
omit h [Enc C]
namespace Groundwork.Prog.NetE
theorem _root_.solution (Np : PNet C) (c : C) : Pc g Np c ≤ Uc g Np c := by
  unfold Pc Uc
  generalize (List.range g).map (rowSum g Np c) = l
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, List.sum_cons]; omega
end Groundwork.Prog.NetE
