-- Prove2me | solution 1 for Groundwork.DecodeK.IsKCNF.length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:29:31.581868+00:00
-- url     : https://prove2.me/submissions/1f8cd260-d013-4914-9b4a-3d54691ffcf5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_WidthK_Decode
import Theorems.Thm_Groundwork_DecodeK_eq_of_slots
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Sat3_eq_of_slots
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode
namespace Groundwork.DecodeK
namespace IsKCNF
theorem _root_.solution {k n : ℕ} {φ : CNF n} (h : IsKCNF k φ) : φ.length ≤ (2 * n + 1) ^ k := by
  have := (h.2.map_on (f := fun C (j : Fin k) => C[(j : ℕ)]?) fun C hC D hD e =>
    eq_of_slots (h.1 C hC) (h.1 D hD) fun j hj => congrFun e ⟨j, hj⟩).length_le_card
  simpa [mul_comm] using this
end IsKCNF
end Groundwork.DecodeK
