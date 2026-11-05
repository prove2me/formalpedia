-- Prove2me | solution 1 for GeneralPieces.Dual.aFam_op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:24:27.589163+00:00
-- url     : https://prove2.me/submissions/b54057ab-7d01-42ed-9653-f29db6c7d39b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_sgn_mul_self
import Theorems.Thm_GeneralPieces_Dual_display_single
import Theorems.Thm_GeneralPieces_Dual_aFam_eq
import Theorems.Thm_GeneralPieces_opFacts


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (h : ℕ) (μ : List ℕ+) (hμ : wt (μ : Multiset ℕ+) = h) (b : V) (hb : b ∈ VE h) :
    op (aFam (μ : Multiset ℕ+)) (-(h : ℤ)) b = nablas (μ.map fun n : ℕ+ => (n : ℤ)) b := by
  rw [aFam_eq, opFacts.smul_left, display_single h μ hμ b hb, smul_smul]
  have : (sgn μ : ℚ) * (sgn μ : ℚ) = 1 := by exact_mod_cast sgn_mul_self μ
  rw [this, one_smul]
end GeneralPieces.Dual
