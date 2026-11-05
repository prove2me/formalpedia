-- Prove2me | solution 1 for GeneralPieces.GenF.DD_tT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:58:59.113553+00:00
-- url     : https://prove2.me/submissions/7571a66c-864c-4d4f-83a3-ef0fec871b8d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_JmT_tT
import Theorems.Thm_GeneralPieces_GenF_map_sel
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
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (i : X) (k : ℕ) : DD rd i (tT k) = emb ((k : ℚ) • sel rd (fun n => (bet n (-(k : ℤ)) : ℚ) • mo (-(k : ℤ) - n) 0) 0 i) := by
  rw [DD, map_sel (fun d : Derivation ℚ Tv Tv => d (tT k)) rfl, map_sel (fun s : S => emb ((k : ℚ) • s)) (by simp)]
  congr 1
  · funext n
    exact JmT_tT n k
  · funext n
    simp
end GeneralPieces.GenF
