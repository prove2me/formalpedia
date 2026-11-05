-- Prove2me | solution 1 for GeneralPieces.GenF.aL_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:05:39.845338+00:00
-- url     : https://prove2.me/submissions/5575c873-ab05-4e31-961e-e161e9e43991

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution {ι : ℕ → X} {a : List ℕ} {i : X} (h : aL ι a i ≠ 0) : ∃ n ∈ a, i = ι n := by
  classical
  induction a with
  | nil => exact absurd rfl h
  | cons n a ih =>
    unfold aL at h ih
    rw [List.map_cons, List.sum_cons, Finsupp.add_apply] at h
    by_cases h1 : Finsupp.single (ι n) 1 i = 0
    · rw [h1, zero_add] at h
      obtain ⟨m, hm, e⟩ := ih h
      exact ⟨m, List.mem_cons_of_mem _ hm, e⟩
    · rw [Finsupp.single_apply] at h1
      have h2 : ι n = i := by
        by_contra h2
        exact h1 (if_neg h2)
      exact ⟨n, List.mem_cons_self, h2.symm⟩
end GeneralPieces.GenF
