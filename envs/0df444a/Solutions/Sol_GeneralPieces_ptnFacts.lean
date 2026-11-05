-- Prove2me | solution 1 for GeneralPieces.ptnFacts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:23:29.859232+00:00
-- url     : https://prove2.me/submissions/21b077e5-423b-443b-abf4-56f2bde54ce0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_GeneralPieces_Ring_mem_ptns
import Theorems.Thm_GeneralPieces_Ring_card_ptns
import Theorems.Thm_ClauseBound_Part_p_mono


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces Finset GeneralPieces.Ring
namespace GeneralPieces
theorem _root_.solution : PtnFacts where
  mem := mem_ptns
  card := card_ptns
  mono := fun E => ClauseBound.Part.p_mono (Nat.le_succ E)
end GeneralPieces
