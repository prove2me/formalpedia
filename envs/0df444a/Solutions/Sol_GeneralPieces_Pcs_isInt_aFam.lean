-- Prove2me | solution 1 for GeneralPieces.Pcs.isInt_aFam
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:01:59.857817+00:00
-- url     : https://prove2.me/submissions/ef406d8f-07f0-48ad-8b85-260ec23ae572

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

private theorem one_eq_tpow_aux : (1 : V) = tpow 0 := by
  unfold tpow
  rw [map_zero]
  rfl

private theorem X_eq_tpow_aux (k : ℕ+) : (X k : V) = tpow {k} := by
  unfold tpow
  rw [Multiset.toFinsupp_singleton]
  rfl

private theorem aFam_zero_aux : aFam 0 = 1 := by
  simp [aFam]

private theorem aFam_cons_aux (n : ℕ+) (μ : Ptn) :
    aFam (n ::ₘ μ) = ((-1 : ℚ) ^ ((n : ℕ) - 1) • y n) * aFam μ := by
  unfold aFam
  rw [Multiset.map_cons, Multiset.prod_cons]

private theorem isInt_add_aux {f g : V} (hf : IsInt f) (hg : IsInt g) :
    IsInt (f + g) := fun m => by
  obtain ⟨z, hz⟩ := hf m
  obtain ⟨w, hw⟩ := hg m
  exact ⟨z + w, by rw [coeff_add, hz, hw]; push_cast; rfl⟩

private theorem isInt_zero_aux : IsInt (0 : V) := fun m => ⟨0, by simp⟩

private theorem isInt_sum_aux {ι : Type} (s : Finset ι) {F : ι → V}
    (hF : ∀ i ∈ s, IsInt (F i)) : IsInt (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isInt_zero_aux
  | insert x s hx ih =>
    rw [sum_insert hx]
    exact isInt_add_aux (hF x (mem_insert_self _ _))
      (ih fun i hi => hF i (mem_insert_of_mem hi))

private theorem isInt_smul_aux {f : V} (hf : IsInt f) (z : ℤ) :
    IsInt ((z : ℚ) • f) := fun m => by
  obtain ⟨w, hw⟩ := hf m
  exact ⟨z * w, by rw [coeff_smul, hw, smul_eq_mul]; push_cast; rfl⟩

private theorem isInt_mul_aux {f g : V} (hf : IsInt f) (hg : IsInt g) :
    IsInt (f * g) := fun m => by
  classical
  choose zf hzf using hf
  choose zg hzg using hg
  refine ⟨∑ x ∈ antidiagonal m, zf x.1 * zg x.2, ?_⟩
  rw [coeff_mul]
  push_cast
  exact sum_congr rfl fun x _ => by rw [hzf, hzg]

private theorem isInt_tpow_aux (μ : Ptn) : IsInt (tpow μ) := fun m => by
  classical
  unfold tpow
  rw [coeff_monomial]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

private theorem isInt_y_aux (n : ℕ+) : IsInt (y n) := by
  unfold y
  refine isInt_sum_aux _ fun j _ => ?_
  have := isInt_smul_aux (isInt_tpow_aux {j.toPNat'}) ((n : ℕ).choose j : ℤ)
  rwa [Int.cast_natCast, ← X_eq_tpow_aux] at this

theorem solution (μ : Ptn) : IsInt (aFam μ) := by
  induction μ using Multiset.induction_on with
  | empty =>
    rw [aFam_zero_aux, one_eq_tpow_aux]
    exact isInt_tpow_aux 0
  | cons n μ ih =>
    rw [aFam_cons_aux]
    have := isInt_smul_aux (isInt_y_aux n) ((-1) ^ ((n : ℕ) - 1))
    push_cast at this
    exact isInt_mul_aux this ih
