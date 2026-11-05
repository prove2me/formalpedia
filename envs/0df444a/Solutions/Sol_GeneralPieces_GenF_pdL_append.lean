-- Prove2me | solution 1 for GeneralPieces.GenF.pdL_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:57:33.913334+00:00
-- url     : https://prove2.me/submissions/e0b3770c-9f7b-4933-a179-6b932b04ec0e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
import Theorems.Thm_GeneralPieces_GenF_pdL_cons

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
namespace GeneralPieces.GenF
theorem _root_.solution (L L' : List Y) (F : MvPowerSeries Y R) : pdL (L ++ L') F = pdL L' (pdL L F) := by
  induction L generalizing F with
  | nil => rfl
  | cons i L ih => rw [List.cons_append, pdL_cons, pdL_cons, ih]
end GeneralPieces.GenF
