-- Prove2me | solution 1 for GeneralPieces.GenF.fac_add_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:46:55.4722+00:00
-- url     : https://prove2.me/submissions/5c82f145-1278-4922-b032-647fba00fc9f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Mathlib.Data.Finsupp.Multiset
import Definitions.Def_GeneralPieces_GenF_Coeff

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (α : X →₀ ℕ) (i : X) : fac (α + Finsupp.single i 1) = ((α i : ℚ) + 1) * fac α := by
  classical
  have hs1 : (α + Finsupp.single i 1).support ⊆ insert i α.support := by
    refine Finsupp.support_add.trans (union_subset (subset_insert _ _) ?_)
    exact Finsupp.support_single_subset.trans (singleton_subset_iff.2 (mem_insert_self _ _))
  have key : ∀ β : X →₀ ℕ, β.support ⊆ insert i α.support → fac β = ∏ v ∈ insert i α.support, ((β v).factorial : ℚ) :=
    fun β h => Finsupp.prod_of_support_subset β h _ fun _ _ => by simp
  have h2 : ∏ v ∈ (insert i α.support).erase i, ((((α + Finsupp.single i 1 : X →₀ ℕ)) v).factorial : ℚ) = ∏ v ∈ (insert i α.support).erase i, ((α v).factorial : ℚ) :=
    prod_congr rfl fun v hv => by rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (ne_of_mem_erase hv), add_zero]
  rw [key _ hs1, key α (subset_insert _ _), ← mul_prod_erase _ _ (mem_insert_self i _), ← mul_prod_erase _ (fun v => ((α v).factorial : ℚ)) (mem_insert_self i _), h2,
    Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring
end GeneralPieces.GenF
