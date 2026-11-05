-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_opX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:46:32.880197+00:00
-- url     : https://prove2.me/submissions/b612c2fd-1418-42f9-a677-32527b1d4f96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Theorems.Thm_GeneralPieces_GenF_pderiv_mapE

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (O : X → A →ₗ[ℚ] A) (i : X) (f : MvPowerSeries X A) : pderiv A i (opX O f) = opX O (pderiv A i f) + mapE (O i) f := by
  classical
  ext α
  have hs1 : (α + Finsupp.single i 1).support ⊆ insert i α.support := by
    refine Finsupp.support_add.trans (union_subset (subset_insert _ _) ?_)
    exact Finsupp.support_single_subset.trans (singleton_subset_iff.2 (mem_insert_self _ _))
  have h : ∀ v, pderiv A i (MvPowerSeries.X v * mapE (O v) f) = MvPowerSeries.X v * mapE (O v) (pderiv A i f) + if v = i then mapE (O v) f else 0 := fun v => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_mapE]
    split_ifs with hv
    · rw [hv, pderiv_X_self, mul_one]
    · rw [pderiv_X_of_ne hv, mul_zero]
  rw [coeff_pderiv, coeff_opX_eq O f hs1, ← coeff_pderiv, map_sum]
  simp only [h]
  rw [sum_add_distrib, sum_ite_eq' _ i, if_pos (mem_insert_self _ _), map_add, map_add, ← coeff_opX_eq O _ (subset_insert _ _)]
end GeneralPieces.GenF
