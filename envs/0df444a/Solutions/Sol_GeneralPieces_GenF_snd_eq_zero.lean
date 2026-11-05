-- Prove2me | solution 1 for GeneralPieces.GenF.snd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:08:43.115227+00:00
-- url     : https://prove2.me/submissions/b902ec82-afc0-4eb4-84b0-e18b07aa9ebd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
import Theorems.Thm_GeneralPieces_GenF_wtX_ex
import Theorems.Thm_GeneralPieces_GenF_eq_zero_of_wtX

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution {a b : List ℕ} (ha : Pos a) (hb : Pos b) {p : (X →₀ ℕ) × (X →₀ ℕ)} (hp : p ∈ antidiagonal (ex a b)) (hw : wtX p.1 = a.sum + b.sum) :
    p.2 = 0 := by
  have e := mem_antidiagonal.1 hp
  have h1 : wtX p.1 + wtX p.2 = a.sum + b.sum := by rw [← map_add, e, wtX_ex]
  exact eq_zero_of_wtX ha hb (e ▸ le_add_self) (by omega)
end GeneralPieces.GenF
