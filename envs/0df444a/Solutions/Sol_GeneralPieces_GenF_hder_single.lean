-- Prove2me | solution 1 for GeneralPieces.GenF.hder_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:46:26.439101+00:00
-- url     : https://prove2.me/submissions/dba0ea57-b699-49b5-bebe-844a8cccfa2d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Definitions.Def_GeneralPieces_GenF_Hahn
import Theorems.Thm_GeneralPieces_GenF_coeff_hder

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset HahnSeries
variable {A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (d : Derivation ℚ A A) (y : ℤ) (a : A) : hder d (single y a) = single y (d a) := by
  ext z
  rw [coeff_hder]
  by_cases h : z = y
  · rw [h, coeff_single_same, coeff_single_same]
  · rw [coeff_single_of_ne h, coeff_single_of_ne h, map_zero]
end GeneralPieces.GenF
