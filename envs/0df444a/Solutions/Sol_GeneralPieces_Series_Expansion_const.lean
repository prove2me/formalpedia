-- Prove2me | solution 1 for GeneralPieces.Series.Expansion.const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:12:16.979624+00:00
-- url     : https://prove2.me/submissions/256e0545-7860-4900-9e2f-101dc14348ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
import Theorems.Thm_GeneralPieces_Series_mul2_vac
import Theorems.Thm_GeneralPieces_Series_Expansion_fP_vac
import Theorems.Thm_GeneralPieces_Series_cfP_epsP_pow
import Theorems.Thm_GeneralPieces_Series_cfP_fP
import Theorems.Thm_GeneralPieces_Series_cf_smul
attribute [local simp] GeneralPieces.Series.cf_smul



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ}
namespace GeneralPieces.Series
namespace Expansion
theorem _root_.solution (X : Expansion a b G 0 0) (hb : Pos b) : G = op a (-(b.sum : ℤ)) 0 (b : Multiset ℕ) := by
  have h1 : cfP (fP a b 0 0) (-((a.sum + b.sum : ℕ) : ℤ)) 0 = G := by
    rw [X.fP_vac, cfP, cf_smul, ← cfP, cfP_epsP_pow, mul_one]
  rw [cfP_fP, if_pos (by push_cast; ring), show -((a.sum + b.sum : ℕ) : ℤ) + a.sum = -(b.sum : ℤ) by push_cast; ring, zero_add, mul2_vac a hb] at h1
  exact h1.symm
end Expansion
end GeneralPieces.Series
