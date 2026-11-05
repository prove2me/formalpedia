-- Prove2me | solution 1 for GeneralPieces.GenF.sum_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:24:13.018977+00:00
-- url     : https://prove2.me/submissions/058b590a-3f77-42b1-859b-8b3b9d30db0c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralPieces_GenF_Exp

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution {M : Type} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) (h : ∀ i j, N ≤ i + j → F i j = 0) :
    ∑ n ∈ range N, ∑ p ∈ antidiagonal n, F p.1 p.2 = ∑ i ∈ range N, ∑ j ∈ range N, F i j := by
  rw [← sum_product' (range N) (range N) F]
  have h1 : ∑ p ∈ range N ×ˢ range N, F p.1 p.2 = ∑ p ∈ (range N ×ˢ range N) with p.1 + p.2 < N, F p.1 p.2 := by
    rw [sum_filter]
    refine sum_congr rfl fun p _ => ?_
    split_ifs with hp
    · rfl
    · exact h p.1 p.2 (by omega)
  rw [h1, ← sum_fiberwise_of_maps_to (t := range N) (g := fun p : ℕ × ℕ => p.1 + p.2) fun p hp => mem_range.2 (mem_filter.1 hp).2]
  refine sum_congr rfl fun n hn => sum_congr ?_ fun _ _ => rfl
  have hn' := mem_range.1 hn
  ext p
  simp only [mem_antidiagonal, mem_filter, mem_product, mem_range]
  omega
end GeneralPieces.GenF
