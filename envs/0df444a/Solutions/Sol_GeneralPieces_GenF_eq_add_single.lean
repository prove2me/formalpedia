-- Prove2me | solution 1 for GeneralPieces.GenF.eq_add_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:28:09.748029+00:00
-- url     : https://prove2.me/submissions/afa43c95-d571-404b-9aa0-64bc0a235599

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
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
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution {α : X →₀ ℕ} (hα : α.degree = 2) {i i' : X} (hi : i ∈ α.support) (hi' : i' ∈ α.support) (hne : i ≠ i') :
    α = Finsupp.single i 1 + Finsupp.single i' 1 := by
  classical
  have h1 : 1 ≤ α i := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
  have h2 : 1 ≤ α i' := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi')
  have hle : Finsupp.single i 1 + Finsupp.single i' 1 ≤ α := by
    intro x
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with a b b
    · exact absurd (a.trans b.symm) hne
    · subst a
      simpa using h1
    · subst b
      simpa using h2
    · simp
  obtain ⟨γ, hγ⟩ := exists_add_of_le hle
  have hd : γ.degree = 0 := by
    have := congrArg Finsupp.degree hγ
    rw [map_add, map_add, Finsupp.degree_single, Finsupp.degree_single, hα] at this
    omega
  rw [Finsupp.degree_eq_zero_iff] at hd
  rw [hγ, hd, add_zero]
end GeneralPieces.GenF
