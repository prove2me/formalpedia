-- Prove2me | solution 1 for GeneralPieces.Ring.nabla_pos_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:36:07.56777+00:00
-- url     : https://prove2.me/submissions/93351326-2c3b-4278-99bf-e2c15e988d32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_nabla_pos
import Theorems.Thm_GeneralPieces_Ring_toFinsupp_erase
import Theorems.Thm_ClauseBound_Boson_Text_toFinsupp_erase


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {k : ℤ} (hk : 0 < k) (σ : Ptn) : nabla k (tpow σ) = ((k : ℚ) * σ.count (pn k)) • tpow (σ.erase (pn k)) := by
  rw [nabla_pos hk]
  unfold tpow
  rw [pderiv_monomial, toFinsupp_erase, Multiset.toFinsupp_apply, smul_monomial, smul_monomial]
  simp
end GeneralPieces.Ring
