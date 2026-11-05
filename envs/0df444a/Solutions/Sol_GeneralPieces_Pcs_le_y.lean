-- Prove2me | solution 1 for GeneralPieces.Pcs.le_y
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:23:59.315014+00:00
-- url     : https://prove2.me/submissions/09bcc516-164b-4d1a-bc7d-62ca2dc67623

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

namespace GeneralPieces

private theorem coef_add' (π : Ptn) (a b : V) : coef π (a + b) = coef π a + coef π b := by
  unfold coef
  rw [coeff_add]

private theorem coef_smul' (π : Ptn) (q : ℚ) (f : V) : coef π (q • f) = q * coef π f := by
  unfold coef
  rw [coeff_smul, smul_eq_mul]

private theorem coef_zero' (π : Ptn) : coef π (0 : V) = 0 := by
  unfold coef
  rw [coeff_zero]

private theorem coef_tpow' (π σ : Ptn) : coef π (tpow σ) = if π = σ then 1 else 0 := by
  unfold coef tpow
  rw [coeff_monomial]
  by_cases h : π = σ
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Multiset.toFinsupp.injective h'.symm)

end GeneralPieces

namespace GeneralPieces.Pcs

private theorem Le.add' {h : ℕ} {a a' : V} (ha : Le h a) (ha' : Le h a') : Le h (a + a') := fun π hπ => by
  by_cases h1 : coef π a = 0
  · exact ha' π (by rwa [GeneralPieces.coef_add', h1, zero_add] at hπ)
  · exact ha π h1

private theorem Le.smul' {h : ℕ} {a : V} (ha : Le h a) (q : ℚ) : Le h (q • a) := fun π hπ =>
  ha π (by rw [GeneralPieces.coef_smul'] at hπ; exact right_ne_zero_of_mul hπ)

private theorem Le.zero' (h : ℕ) : Le h 0 := fun π hπ => absurd (GeneralPieces.coef_zero' π) hπ

private theorem Le.sum' {ι : Type} {h : ℕ} (s : Finset ι) {F : ι → V}
    (hF : ∀ i ∈ s, Le h (F i)) : Le h (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Le.zero' h
  | insert x s hx ih =>
    rw [sum_insert hx]
    exact (hF x (mem_insert_self _ _)).add' (ih fun i hi => hF i (mem_insert_of_mem hi))

private theorem le_tpow' {h : ℕ} {μ : Ptn} (hμ : wt μ ≤ h) : Le h (tpow μ) := fun π hπ => by
  rw [GeneralPieces.coef_tpow'] at hπ
  by_cases e : π = μ
  · rw [e]; exact hμ
  · rw [if_neg e] at hπ; exact absurd rfl hπ

private theorem X_eq_tpow' (k : ℕ+) : (X k : V) = tpow {k} := by
  unfold tpow
  rw [Multiset.toFinsupp_singleton]
  rfl

private theorem wt_singleton' (k : ℕ+) : wt {k} = k := by simp [wt]

end GeneralPieces.Pcs

theorem solution (n : ℕ+) : Le n (y n) := by
  unfold y
  refine GeneralPieces.Pcs.Le.sum' _ fun j hj => GeneralPieces.Pcs.Le.smul' ?_ _
  rw [GeneralPieces.Pcs.X_eq_tpow']
  refine GeneralPieces.Pcs.le_tpow' ?_
  rw [GeneralPieces.Pcs.wt_singleton', PNat.toPNat'_coe (by have := (mem_Icc.1 hj).1; omega)]
  exact (mem_Icc.1 hj).2
