-- Prove2me | solution 1 for GeneralPieces.GenF.wtX_ex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:07:28.09389+00:00
-- url     : https://prove2.me/submissions/ddf2a79d-45b3-4cde-aa20-0be2db54d433

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
import Theorems.Thm_GeneralPieces_GenF_wtX_list_inl
import Theorems.Thm_GeneralPieces_GenF_wtX_list_inr


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (a b : List ℕ) : wtX (ex a b) = a.sum + b.sum := by
  rw [ex, map_add, aL, aL, wtX_list_inl, wtX_list_inr]
end GeneralPieces.GenF
