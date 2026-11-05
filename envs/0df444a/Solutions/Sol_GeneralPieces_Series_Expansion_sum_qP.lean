-- Prove2me | solution 1 for GeneralPieces.Series.Expansion.sum_qP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:14:39.430677+00:00
-- url     : https://prove2.me/submissions/dd658113-cab3-478e-98c8-d321cd364231

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
import Theorems.Thm_GeneralPieces_Series_Expansion_F_eq
import Theorems.Thm_GeneralPieces_Series_Expansion_ev_F
import Theorems.Thm_GeneralPieces_Series_ev_W


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
namespace Expansion
theorem _root_.solution (X : Expansion a b G π σ) (hab : a.sum ≤ b.sum) :
    ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), (qP a b s π σ : ℚ) = if π = σ then G else 0 := by
  rw [← X.ev_F, X.F_eq hab, map_sum]
  exact sum_congr rfl fun s _ => by rw [map_smul, ev_W, smul_eq_mul, mul_one]
end Expansion
end GeneralPieces.Series
