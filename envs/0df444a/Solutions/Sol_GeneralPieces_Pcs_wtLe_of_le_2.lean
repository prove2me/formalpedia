-- Prove2me | solution 2 for GeneralPieces.Pcs.wtLe_of_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:30:35.44948+00:00
-- url     : https://prove2.me/submissions/40368e32-774d-485a-a57f-ff251731940e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

private theorem weight_toFinsupp_aux (μ : Ptn) :
    Finsupp.weight wgt (Multiset.toFinsupp μ) = wt μ := by
  induction μ using Multiset.induction_on with
  | empty => simp [wt]
  | cons a s ih =>
    rw [← Multiset.singleton_add, map_add, map_add, ih, Multiset.toFinsupp_singleton,
      Finsupp.weight_single]
    simp [wt, wgt]

private theorem ext_coef_aux {f g : V} (h : ∀ π, coef π f = coef π g) : f = g := by
  ext d
  have hd := h (Finsupp.toMultiset d)
  unfold coef at hd
  rwa [Finsupp.toMultiset_toFinsupp] at hd

private theorem coef_sum_aux {ι : Type} (π : Ptn) (s : Finset ι) (F : ι → V) :
    coef π (∑ i ∈ s, F i) = ∑ i ∈ s, coef π (F i) := coeff_sum _ _ _

private theorem coef_part_aux (π : Ptn) (h' : ℕ) (a : V) :
    coef π (part h' a) = if wt π = h' then coef π a else 0 := by
  unfold coef part
  rw [coeff_weightedHomogeneousComponent]
  have hw := weight_toFinsupp_aux π
  unfold wgt at hw
  rw [hw]

theorem solution {h : ℕ} {a : V} (ha : Le h a) : WtLe h a := by
  unfold WtLe
  refine ext_coef_aux fun π => ?_
  rw [coef_sum_aux]
  simp only [coef_part_aux]
  rw [sum_ite_eq]
  split_ifs with hm
  · rfl
  · by_contra hne
    exact hm (mem_range.2 (by have := ha π hne; omega))
