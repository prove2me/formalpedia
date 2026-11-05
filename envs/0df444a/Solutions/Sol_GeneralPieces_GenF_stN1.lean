-- Prove2me | solution 1 for GeneralPieces.GenF.stN1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:55:34.023469+00:00
-- url     : https://prove2.me/submissions/7ef551c1-d2d7-4ee3-be13-330141865181

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
import Theorems.Thm_GeneralPieces_GenF_toP_cL
import Theorems.Thm_GeneralPieces_GenF_toM_cL
import Theorems.Thm_GeneralPieces_GenF_coeff_add_single
import Theorems.Thm_GeneralPieces_GenF_stN2
import Theorems.Thm_GeneralPieces_GenF_coeff_rhs
import Theorems.Thm_GeneralPieces_GenF_sum_erase_le_of_le
import Theorems.Thm_GeneralPieces_GenF_induction_single
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
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution (hN : StNeq) : StN1 := by
  intro E σ σ' γ hσ
  suffices H : ∀ γ : X →₀ ℕ, ∀ σ σ' : Multiset ℕ, ∃ n : L, σ.sum ≤ E →
      MvPowerSeries.coeff γ (normal false E σ σ') = toP n ∧ MvPowerSeries.coeff γ (normal true E σ σ') = toM n by
    obtain ⟨n, hn⟩ := H γ σ σ'
    exact ⟨n, hn hσ⟩
  intro γ
  induction γ using induction_single with
  | h0 =>
    intro σ σ'
    refine ⟨if σ = σ' then 1 else 0, fun _ => ?_⟩
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, stN2, stN2]
    split_ifs <;> simp
  | hs γ i ih =>
    intro σ σ'
    choose nf hnf using ih
    refine ⟨((γ i : ℚ) + 1)⁻¹ • (∑ l ∈ σ.toFinset, cL i l * nf (σ.erase l) σ' +
      ∑ k ∈ σ'.toFinset, (((k : ℚ) * σ'.count k) • cL i (-(k : ℤ))) * nf σ (σ'.erase k)), fun hσ => ⟨?_, ?_⟩⟩
    · rw [coeff_add_single, hN false E σ σ' i hσ, coeff_rhs, map_smul, map_add, map_sum, map_sum]
      congr 2
      · exact Finset.sum_congr rfl fun l _ => by rw [map_mul, toP_cL, (hnf _ _ (sum_erase_le_of_le hσ l)).1]
      · exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_smul, toP_cL, (hnf _ _ hσ).1]
    · rw [coeff_add_single, hN true E σ σ' i hσ, coeff_rhs, map_smul, map_add, map_sum, map_sum]
      congr 2
      · exact Finset.sum_congr rfl fun l _ => by rw [map_mul, toM_cL, (hnf _ _ (sum_erase_le_of_le hσ l)).2]
      · exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_smul, toM_cL, (hnf _ _ hσ).2]
end GeneralPieces.GenF
