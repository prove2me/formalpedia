-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_linear_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:49:13.789033+00:00
-- url     : https://prove2.me/submissions/473edb44-6555-4c6d-802b-ef40285c8cc8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_eq_single_of_degree
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
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution {p : Vu} (hp : ∀ m, MvPolynomial.coeff m p ≠ 0 → m.degree = 1) (q : Vu) (m : ℕ →₀ ℕ) :
    MvPolynomial.coeff m (p * q) = ∑ l ∈ m.support, MvPolynomial.coeff (Finsupp.single l 1) p * MvPolynomial.coeff (m - Finsupp.single l 1) q := by
  classical
  rw [MvPolynomial.coeff_mul]
  have hinj : Set.InjOn (fun l : ℕ => ((Finsupp.single l 1 : ℕ →₀ ℕ), m - Finsupp.single l 1)) m.support := fun a _ b _ hab => by
    have := congrArg Prod.fst hab
    exact (Finsupp.single_left_injective one_ne_zero) this
  rw [← Finset.sum_image (f := fun x : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) => MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q) hinj]
  symm
  refine Finset.sum_subset (fun x hx => ?_) fun x hx hn => ?_
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal, add_comm]
    exact sub_single_add hl
  · by_contra hne
    obtain ⟨l, hl⟩ := eq_single_of_degree (hp x.1 (left_ne_zero_of_mul hne))
    have hsum : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    refine hn (Finset.mem_image.2 ⟨l, ?_, ?_⟩)
    · rw [Finsupp.mem_support_iff, ← hsum, hl]
      simp
    · refine Prod.ext hl.symm ?_
      rw [← hsum, hl]
      simp
end GeneralPieces.GenF
