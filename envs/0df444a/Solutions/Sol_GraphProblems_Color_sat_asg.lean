-- Prove2me | solution 1 for GraphProblems.Color.sat_asg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:13:49.215094+00:00
-- url     : https://prove2.me/submissions/81cf6dfc-b4cf-4d6e-8673-50b9e40bda7c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color
import Theorems.Thm_GraphProblems_Color_sat_colorF
import Theorems.Thm_GraphProblems_Color_ext_asg

set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Color
open Blocks
namespace GraphProblems.Color
theorem _root_.solution (hAdj : StAdj) {n k : ℕ} (G : SimpleGraph (Fin n)) (col : G.Coloring (Fin k)) : Sat (ext (asg col)) (colorF k n (matrix G)) := by
  rw [sat_colorF]
  refine ⟨fun v hv => ⟨col ⟨v, hv⟩, (col ⟨v, hv⟩).2, ?_⟩, fun v hv c₁ h1 c₂ h2 h12 => ?_, fun u hu v hv huv c hc => ?_⟩
  · rw [ext_asg col ⟨v, hv⟩ (col ⟨v, hv⟩).2, decide_eq_true rfl]
  · rw [ext_asg col ⟨v, hv⟩ h1, ext_asg col ⟨v, hv⟩ h2, decide_eq_false_iff_not, decide_eq_false_iff_not]
    omega
  · have h3 : col ⟨u, hu⟩ ≠ col ⟨v, hv⟩ := col.valid ((hAdj n G ⟨u, hu⟩ ⟨v, hv⟩).1 huv)
    have h4 : (col ⟨u, hu⟩).val ≠ (col ⟨v, hv⟩).val := fun h => h3 (Fin.ext h)
    rw [ext_asg col ⟨u, hu⟩ hc, ext_asg col ⟨v, hv⟩ hc, decide_eq_false_iff_not, decide_eq_false_iff_not]
    omega
end GraphProblems.Color
