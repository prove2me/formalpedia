-- Prove2me | solution 1 for GeneralPieces.GenF.pdL_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:57:38.180898+00:00
-- url     : https://prove2.me/submissions/27824263-f9d5-4ac1-bb08-3546188ccdda

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
import Theorems.Thm_GeneralPieces_GenF_pdL_add
import Theorems.Thm_GeneralPieces_GenF_pdL_zero

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
namespace GeneralPieces.GenF
theorem _root_.solution {ι : Type} (L : List Y) (s : Finset ι) (F : ι → MvPowerSeries Y R) : pdL L (∑ j ∈ s, F j) = ∑ j ∈ s, pdL L (F j) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, pdL_zero]
  | insert j s hj ih => rw [sum_insert hj, sum_insert hj, pdL_add, ih]
end GeneralPieces.GenF
