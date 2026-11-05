-- Prove2me | solution 1 for GeneralPieces.GenF.borel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:58:11.286824+00:00
-- url     : https://prove2.me/submissions/ae94e0f9-34f6-4fcc-817c-30f21f1efce1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
import Theorems.Thm_GeneralPieces_GenF_expo_nil
import Theorems.Thm_GeneralPieces_GenF_expo_cons
import Theorems.Thm_GeneralPieces_GenF_pdL_nil
import Theorems.Thm_GeneralPieces_GenF_pdL_cons
import Theorems.Thm_GeneralPieces_GenF_borel_step

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
variable [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution (L : List Y) : ∀ (β : Y →₀ ℕ) (F : MvPowerSeries Y R), fac (β + expo L) • coeff (β + expo L) F = fac β • coeff β (pdL L F) := by
  induction L with
  | nil => intro β F; rw [expo_nil, add_zero, pdL_nil]
  | cons i L ih =>
    intro β F
    rw [expo_cons, add_left_comm, add_comm (Finsupp.single i 1), borel_step, ih, pdL_cons]
end GeneralPieces.GenF
