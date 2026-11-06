-- Prove2me | solution 1 for GraphProblems.readF_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:00:30.690111+00:00
-- url     : https://prove2.me/submissions/ba18530c-f507-44cd-ae4e-46019604d9c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Definitions.Def_GraphProblems_SetTM
import Theorems.Thm_GraphProblems_readF_aux
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Turing
namespace GraphProblems
theorem _root_.solution (hR : StCertRead) {F : ℕ → List Bool → Fml} (hF : PolyT fun a : List Unit × List Bool => F a.1.length a.2) :
    PolyT (readF F) := readF_aux hR.2 hF
end GraphProblems
