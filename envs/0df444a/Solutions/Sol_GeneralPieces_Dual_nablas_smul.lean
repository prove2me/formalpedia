-- Prove2me | solution 1 for GeneralPieces.Dual.nablas_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:22:49.514043+00:00
-- url     : https://prove2.me/submissions/cb5d7b47-56dc-4636-837c-115a82c519a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_nabla_smul
import Theorems.Thm_GeneralPieces_Ring_nabla_smul


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (ks : List ℤ) (q : ℚ) (f : V) : nablas ks (q • f) = q • nablas ks f := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [nablas, List.foldr_cons] at ih ⊢; rw [ih, nabla_smul]
end GeneralPieces.Dual
