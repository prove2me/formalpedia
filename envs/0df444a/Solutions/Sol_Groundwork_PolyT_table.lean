-- Prove2me | solution 1 for Groundwork.PolyT.table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:33:22.318054+00:00
-- url     : https://prove2.me/submissions/d0b7cbeb-63ca-4f35-9520-1e025ccef4bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Definitions.Def_ToTuring_Lib_Table
import Theorems.Thm_Groundwork_PolyT_lookup_eq
import Theorems.Thm_Groundwork_PolyT_lookup_polyT
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε ζ : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε] [Enc ζ]
namespace Groundwork.PolyT
theorem _root_.solution [Finite β] [DecidableEq β] [EqT β] (F : β → γ) : PolyT F := by
  obtain ⟨l, -, hl⟩ := Finite.exists_univ_list β
  rcases isEmpty_or_nonempty β with h | ⟨⟨y₀⟩⟩
  · obtain ⟨P, c, -⟩ := (id' : PolyT fun y : β => y)
    exact ⟨P, c, fun y => isEmptyElim y, fun y => isEmptyElim y⟩
  · exact (lookup_polyT F (F y₀) l).congr fun y => lookup_eq F _ (hl y)
end Groundwork.PolyT
