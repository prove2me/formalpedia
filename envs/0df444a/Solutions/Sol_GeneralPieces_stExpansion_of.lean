-- Prove2me | solution 1 for GeneralPieces.stExpansion_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:10:55.866274+00:00
-- url     : https://prove2.me/submissions/1be333a7-3268-48bf-94dc-cadb34e72edd

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
import Theorems.Thm_GeneralPieces_GenF_snd_eq_zero
import Theorems.Thm_GeneralPieces_GenF_fM_eq_fP
import Theorems.Thm_GeneralPieces_GenF_fP_eq_zero
import Theorems.Thm_GeneralPieces_GenF_compare_plus
import Theorems.Thm_GeneralPieces_GenF_compare_minus
import Theorems.Thm_GeneralPieces_GenF_sum_filter_map
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Series_toP_injective
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces
open GeneralPieces.Series GeneralPieces.GenF ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces
theorem _root_.solution (h15 : StTwoOrders) (hN1 : StN1) (hN2 : StN2) (hN3 : StN3) (hY : StY) : StExpansion := by
  intro a b ha hb
  refine ⟨fac (ex a b) * gam (ex a b), fun π σ hπ hσ => ?_⟩
  by_cases hw : π.sum = σ.sum
  swap
  · have hne : π ≠ σ := fun h => hw (by rw [h])
    exact ⟨{  terms := [(fac (ex a b) * gam (ex a b), a.sum + b.sum, 0)]
              le := fun c hc => by rw [List.mem_singleton.1 hc]
              plus := by simp [fP_eq_zero a b hw]
              minus := by simp [fM_eq_fP, fP_eq_zero b a hw]
              top := fun c hc _ => by rw [List.mem_singleton.1 hc, if_neg hne]
              tot := by simp
              vac := fun h1 h2 => absurd (h1.trans h2.symm) hne }⟩
  choose n hnP hnM using fun γ => hN1 π.sum π σ γ le_rfl
  have hsum : ∀ (ε : S) (φ : L → S), (((antidiagonal (ex a b)).toList.map fun p => (fac (ex a b) * gam p.1, wtX p.1, n p.2)).map
      fun c : ℚ × ℕ × L => c.1 • (ε ^ c.2.1 * φ c.2.2)).sum = fac (ex a b) • ∑ p ∈ antidiagonal (ex a b), (gam p.1 • ε ^ wtX p.1) * φ (n p.2) := by
    intro ε φ
    rw [List.map_map, Finset.sum_map_toList, smul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [Function.comp_apply, smul_mul_assoc, smul_smul]
  refine ⟨{ terms := (antidiagonal (ex a b)).toList.map fun p => (fac (ex a b) * gam p.1, wtX p.1, n p.2)
            le := ?_, plus := ?_, minus := ?_, top := ?_, tot := ?_, vac := ?_ }⟩
  · intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    have e := mem_antidiagonal.1 (mem_toList.1 hp)
    have h1 : wtX p.1 + wtX p.2 = a.sum + b.sum := by rw [← map_add, e, wtX_ex]
    exact h1 ▸ Nat.le_add_right _ _
  · rw [hsum epsP toP, compare_plus h15 hY ha hb hπ hσ hw le_rfl]
    simp_rw [hnP]
  · rw [hsum epsM toM, compare_minus h15 hY ha hb hπ hσ hw le_rfl]
    simp_rw [hnM]
  · intro c hc hH
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    have h0 := snd_eq_zero ha hb (mem_toList.1 hp) hH
    refine toP_injective ?_
    change toP (n p.2) = _
    rw [← hnP, h0, coeff_zero_eq_constantCoeff_apply, hN2]
    split_ifs
    · rw [map_one]
    · rw [map_zero]
  · rw [sum_filter_map, Finset.sum_map_toList]
    rw [Finset.sum_eq_single (ex a b, 0)]
    · rw [if_pos (wtX_ex a b)]
    · intro p hp hne
      refine if_neg fun hH => hne ?_
      have h0 := snd_eq_zero ha hb hp hH
      have e := mem_antidiagonal.1 hp
      rw [h0, add_zero] at e
      exact Prod.ext e h0
    · intro h
      exact absurd (mem_antidiagonal.2 (add_zero _)) h
  · intro hπ0 hσ0 c hc hlt
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    have e := mem_antidiagonal.1 (mem_toList.1 hp)
    have hne : p.2 ≠ 0 := by
      intro h0
      rw [h0, add_zero] at e
      have h1 : wtX p.1 < a.sum + b.sum := hlt
      rw [e, wtX_ex] at h1
      exact lt_irrefl _ h1
    refine toP_injective ?_
    change toP (n p.2) = _
    rw [← hnP, hπ0, hσ0, hN3, map_zero, coeff_one, if_neg hne]
end GeneralPieces
