-- Prove2me | solution 1 for GeneralPieces.Lex.lexNum_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:25:04.580509+00:00
-- url     : https://prove2.me/submissions/14920636-1e2f-4a48-b0fb-3644d15d7a71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_GeneralPieces_Lex_rank_injOn
import Theorems.Thm_GeneralPieces_Lex_desc_injective

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
namespace GeneralPieces.Lex
theorem _root_.solution (h : ℕ) : Set.InjOn (lexNum h) (ptns h) := rank_injOn (ptns h) desc desc_injective.injOn
end GeneralPieces.Lex
