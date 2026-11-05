-- Prove2me | solution 1 for GeneralPieces.GenF.eq_zero_of_wtX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:06:43.492279+00:00
-- url     : https://prove2.me/submissions/7074dc6a-c44a-4725-99a2-374b785b1ef5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
import Theorems.Thm_GeneralPieces_GenF_aL_apply_ne_zero

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution {a b : List ℕ} (ha : Pos a) (hb : Pos b) {γ : X →₀ ℕ} (hγ : γ ≤ ex a b) (h0 : wtX γ = 0) : γ = 0 := by
  ext i
  by_contra hi
  have h1 : ex a b i ≠ 0 := fun h => hi (Nat.le_zero.1 (h ▸ hγ i))
  have h2 : (Sum.elim id id : X → ℕ) i ≠ 0 := by
    rw [ex, Finsupp.add_apply] at h1
    by_cases h3 : aL Sum.inl a i = 0
    · rw [h3, zero_add] at h1
      obtain ⟨n, hn, rfl⟩ := aL_apply_ne_zero h1
      exact (Nat.pos_iff_ne_zero.1 (hb n hn))
    · obtain ⟨n, hn, rfl⟩ := aL_apply_ne_zero h3
      exact (Nat.pos_iff_ne_zero.1 (ha n hn))
  have h4 := Finsupp.le_weight (Sum.elim id id : X → ℕ) h2 γ
  exact hi (Nat.le_zero.1 (h0 ▸ h4))
end GeneralPieces.GenF
