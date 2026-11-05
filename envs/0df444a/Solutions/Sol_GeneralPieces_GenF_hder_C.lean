-- Prove2me | solution 1 for GeneralPieces.GenF.hder_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:47:06.630569+00:00
-- url     : https://prove2.me/submissions/1548ab14-dc82-430c-b48b-d64b45a2ba27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Definitions.Def_GeneralPieces_GenF_Hahn
import Theorems.Thm_GeneralPieces_GenF_hder_single

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset HahnSeries
variable {A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (d : Derivation ℚ A A) (a : A) : hder d (HahnSeries.C a) = HahnSeries.C (d a) := hder_single d 0 a
end GeneralPieces.GenF
