-- Prove2me | solution 1 for GeneralPieces.Series.Expansion.dW_pow_mul_fM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:08:15.23709+00:00
-- url     : https://prove2.me/submissions/2287fb89-1da5-44c3-8a5d-ac1bd9a7c945

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Theorems.Thm_GeneralPieces_Series_pow_mul_terms
import Theorems.Thm_GeneralPieces_Series_dW_mul_epsM


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
namespace Expansion
theorem _root_.solution (X : Expansion a b G π σ) : toM dW ^ (a.sum + b.sum) * fM a b π σ = toM X.F := by
  rw [X.minus, Expansion.F]
  exact pow_mul_terms toM dW_mul_epsM _ _ X.le
end Expansion
end GeneralPieces.Series
