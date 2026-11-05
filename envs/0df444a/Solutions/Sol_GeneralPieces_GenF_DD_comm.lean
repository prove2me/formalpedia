-- Prove2me | solution 1 for GeneralPieces.GenF.DD_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:55:22.89418+00:00
-- url     : https://prove2.me/submissions/8e662f8c-759f-448d-8c3e-3dabb75cf253

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_GenF_DDComm
import Theorems.Thm_GeneralPieces_GenF_JmT_comm
import Theorems.Thm_GeneralPieces_GenF_DD_eq
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (i j : X) (a : Tv) : DD rd i (DD rd j a) = DD rd j (DD rd i a) := by
  rcases DD_eq rd i with hi | ⟨n, hi⟩ <;> rcases DD_eq rd j with hj | ⟨m, hj⟩ <;> rw [hi, hj]
  · simp
  · simp
  · exact JmT_comm n m a
end GeneralPieces.GenF
