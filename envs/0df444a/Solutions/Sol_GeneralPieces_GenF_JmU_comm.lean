-- Prove2me | solution 1 for GeneralPieces.GenF.JmU_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:53:17.961808+00:00
-- url     : https://prove2.me/submissions/83881616-d6aa-4fab-a2a6-c9c4a3ee8e9c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_GenF_DDComm
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
theorem _root_.solution (n m : ℕ) (p : Vu) : JmU n (JmU m p) = JmU m (JmU n p) := by
  have h : ⁅JmU n, JmU m⁆ = 0 := MvPolynomial.derivation_ext fun k => by
    rw [Derivation.commutator_apply, JmU, JmU, MvPolynomial.mkDerivation_X, MvPolynomial.mkDerivation_X, MvPolynomial.derivation_C, MvPolynomial.derivation_C, sub_zero]
    rfl
  have h' := congrArg (fun D : Derivation Lu Vu Vu => D p) h
  simp only [Derivation.commutator_apply] at h'
  exact sub_eq_zero.1 h'
end GeneralPieces.GenF
