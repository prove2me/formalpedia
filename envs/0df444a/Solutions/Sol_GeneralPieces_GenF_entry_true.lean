-- Prove2me | solution 1 for GeneralPieces.GenF.entry_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:06:20.979036+00:00
-- url     : https://prove2.me/submissions/03043382-622e-4d12-95fe-7160eab0d0b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
import Theorems.Thm_GeneralPieces_GenF_wtX_single
import Theorems.Thm_GeneralPieces_GenF_eq_add_single
import Theorems.Thm_GeneralPieces_GenF_kapS_eq_M
import Theorems.Thm_P2M_GeneralPieces_GenF_z0_zero__88981357d0e4
import Theorems.Thm_GeneralPieces_GenF_z0_at_zero
import Theorems.Thm_GeneralPieces_GenF_z0_of_pos
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
theorem _root_.solution {α : X →₀ ℕ} (hα : α.degree = 2) {i i' : X} (hi : i ∈ α.support) (hi' : i' ∈ α.support) :
    sel true (fun p => sel true 0 (fun q => kapS p q) i') 0 i = algebraMap ℚ S (GamX i' i) * epsM ^ wtX α := by
  rcases i with p | p
  · change z0 (0 : ℕ → S) p = _
    rw [z0_zero']
    rcases i' with q | q
    · change 0 = algebraMap ℚ S (z0 (fun q => z0 (0 : ℕ → ℚ) p) q) * _
      simp only [z0_zero']
      rw [show (fun _ : ℕ => (0 : ℚ)) = 0 from rfl, z0_zero', map_zero, zero_mul]
    · change 0 = algebraMap ℚ S (z0 (0 : ℕ → ℚ) q) * _
      rw [z0_zero', map_zero, zero_mul]
  · rcases i' with q | q
    · change z0 (fun p => z0 (fun q => kapS p q) q) p = algebraMap ℚ S (z0 (fun q => z0 (fun p => (Gam q p : ℚ)) p) q) * _
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · rcases Nat.eq_zero_or_pos q with rfl | hq
        · rw [z0_at_zero, z0_at_zero, map_zero, zero_mul]
        · rw [z0_at_zero, z0_of_pos _ hq, z0_at_zero, map_zero, zero_mul]
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · rw [z0_of_pos _ hp, z0_at_zero, z0_at_zero, map_zero, zero_mul]
      rw [z0_of_pos _ hp, z0_of_pos _ hq, z0_of_pos _ hq, z0_of_pos _ hp, kapS_eq_M hp hq, eq_add_single hα hi' hi (by simp), map_add, wtX_single,
        wtX_single, Algebra.smul_def]
      simp
    · change z0 (fun p => z0 (0 : ℕ → S) q) p = algebraMap ℚ S (z0 (0 : ℕ → ℚ) q) * _
      simp only [z0_zero']
      rw [show (fun _ : ℕ => (0 : S)) = 0 from rfl, z0_zero', map_zero, zero_mul]
end GeneralPieces.GenF
