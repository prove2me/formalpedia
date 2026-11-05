-- Prove2me | solution 1 for Groundwork.Grid.bitsOf_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:07:12.384432+00:00
-- url     : https://prove2.me/submissions/6e1e013c-e692-4a7e-9bc5-43be57509b83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
import Theorems.Thm_Groundwork_Code_dec_inj
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution {n : ℕ} {w w' : List Bool} (h : w.length = n) (h' : w'.length = n) :
    bitsOf n w = bitsOf n w' ↔ w = w' :=
  (bitsC n).dec_inj (mem_words.2 h) (mem_words.2 h')
end Groundwork.Grid
