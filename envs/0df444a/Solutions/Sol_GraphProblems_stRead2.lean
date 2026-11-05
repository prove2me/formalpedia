-- Prove2me | solution 1 for GraphProblems.stRead2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:35:53.327346+00:00
-- url     : https://prove2.me/submissions/5cbd94e9-f93e-475c-9e9b-42d88735c0c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
import Theorems.Thm_GraphProblems_Read_ones_unary_append
import Theorems.Thm_GraphProblems_Read_rest_unary_append

set_option autoImplicit false
section
section
open GraphProblems
open Read
namespace GraphProblems
theorem _root_.solution : StRead2 := fun n G s => by
  rw [read2, codeWith, ones_unary_append, rest_unary_append, ones_unary_append, rest_unary_append]
end GraphProblems
