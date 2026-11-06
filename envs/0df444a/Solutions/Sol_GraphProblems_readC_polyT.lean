-- Prove2me | solution 1 for GraphProblems.readC_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:05:00.230431+00:00
-- url     : https://prove2.me/submissions/bcfdae97-f884-4524-893f-43918579758c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_GraphProblems_Sized
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic
import Definitions.Def_GraphProblems_ColorTM
import Theorems.Thm_GraphProblems_readC_aux

set_option autoImplicit false
section
open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Turing
namespace GraphProblems
theorem _root_.solution (hR : StCertRead) (hF : StCertForm) (k : ℕ) : PolyT (readC k) := readC_aux k hR.1 (hF.2.2.2 k)
end GraphProblems
