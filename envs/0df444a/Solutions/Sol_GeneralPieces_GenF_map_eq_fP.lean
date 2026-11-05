-- Prove2me | solution 1 for GeneralPieces.GenF.map_eq_fP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:04:33.082742+00:00
-- url     : https://prove2.me/submissions/30972ba0-36e8-457f-a25f-d83cc15fda59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_YY
import Theorems.Thm_GeneralPieces_GenF_form_eq_sum
import Theorems.Thm_ClauseBound_Boson_mem_Pz
import Theorems.Thm_GeneralPieces_GenF_coeff_smul_mo
import Theorems.Thm_GeneralPieces_Series_mul2_eq_zero


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (h0 : StOp0) {a b : List ℕ} {σ σ' : Multiset ℕ} (hσ' : 0 ∉ σ') (hw : σ.sum = σ'.sum) (ℓ : Vu →ₗ[Lu] Lu)
    (hℓ : ∀ τ : Multiset ℕ, ℓ (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) = C ((op a ((σ.sum : ℤ) - τ.sum) σ τ : ℤ) : ℚ) * T ((σ.sum : ℤ) - τ.sum - a.sum))
    (g : Tv) (hg : ∀ τ : Multiset ℕ, bra τ g = ((op b ((τ.sum : ℤ) - σ'.sum) τ σ' : ℤ) : ℚ) • mo 0 ((τ.sum : ℤ) - σ'.sum - b.sum)) :
    g.map ℓ = fP a b σ σ' := by
  classical
  ext y : 2
  change ℓ (g.coeff y) = _
  have hc : ∀ τ : Multiset ℕ, MvPolynomial.coeff (Multiset.toFinsupp τ) (g.coeff y) =
      if y = (τ.sum : ℤ) - σ'.sum - b.sum then C ((op b ((τ.sum : ℤ) - σ'.sum) τ σ' : ℤ) : ℚ) else 0 := fun τ => by
    rw [← coeff_bra, hg, coeff_smul_mo, T_zero, mul_one]
  have hw' : (σ.sum : ℤ) = σ'.sum := by exact_mod_cast hw
  have key : ℓ (g.coeff y) = C ((mul2 a (-y - b.sum) b (y + b.sum) σ σ' : ℤ) : ℚ) * T (-((a.sum : ℤ) + b.sum) - y) := by
    have e1 : ∑ m ∈ (g.coeff y).support, MvPolynomial.coeff m (g.coeff y) * ℓ (MvPolynomial.monomial m 1) =
        ∑ τ ∈ (g.coeff y).support.image Finsupp.toMultiset,
          MvPolynomial.coeff (Multiset.toFinsupp τ) (g.coeff y) * ℓ (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) := by
      rw [sum_image fun m _ m' _ h => by
        have h' := congrArg Multiset.toFinsupp h
        rwa [Finsupp.toMultiset_toFinsupp, Finsupp.toMultiset_toFinsupp] at h']
      exact sum_congr rfl fun m _ => by rw [Finsupp.toMultiset_toFinsupp]
    rw [form_eq_sum, e1, mul2, Int.cast_sum, map_sum, sum_mul]
    refine sum_congr_of_eq_on_inter (fun τ _ h2 => ?_) (fun τ h1 h2 => ?_) fun τ _ h2 => ?_
    · rw [hc]
      split_ifs with hy
      · have h3 : 0 ∈ τ := by
          by_contra h3
          exact h2 (mem_Pz.2 ⟨by omega, h3⟩)
        rw [h0 b _ τ σ' h3 hσ', Int.cast_zero, map_zero, zero_mul]
      · rw [zero_mul]
    · have h3 := (mem_Pz.1 h1).1
      have h4 : MvPolynomial.coeff (Multiset.toFinsupp τ) (g.coeff y) = 0 := by
        by_contra h4
        exact h2 (mem_image.2 ⟨Multiset.toFinsupp τ, MvPolynomial.mem_support_iff.2 h4, Multiset.toFinsupp_toMultiset τ⟩)
      rw [hc, if_pos (by omega), show (τ.sum : ℤ) - σ'.sum = y + b.sum by omega] at h4
      rw [Int.cast_mul, map_mul, h4, mul_zero, zero_mul]
    · have h3 := (mem_Pz.1 h2).1
      rw [hc, if_pos (by omega), hℓ, show (τ.sum : ℤ) - σ'.sum = y + b.sum by omega, show (σ.sum : ℤ) - τ.sum = -y - b.sum by omega,
        show -y - (b.sum : ℤ) - a.sum = -((a.sum : ℤ) + b.sum) - y by ring, Int.cast_mul, map_mul]
      ring
  rw [key, fP, Series.diag, HahnSeries.coeff_ofSuppBddBelow]
  split_ifs with hy
  · rfl
  · rw [mul2_eq_zero a b _ σ (by omega), Int.cast_zero, map_zero, zero_mul]
end GeneralPieces.GenF
