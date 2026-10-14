-- Prove2me | solution 1 for IntMul.HvdH.agarwal_cooley_poly
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T20:42:47.899275+00:00
-- url     : https://prove2.me/submissions/0dbf61b5-1ecf-4214-9c2f-fb2c6a575a63

import Mathlib

open Polynomial

theorem cyclic_coeff_mul {R : Type} [CommRing R] (S : ℕ) [NeZero S] (F G : R[X])
    (hdeg : F.natDegree + G.natDegree < S) (j : ℕ) (hj : j < S) :
    (F * G).coeff j = ∑ k : ZMod S, F.coeff k.val * G.coeff ((j : ZMod S) - k).val := by
  -- sum over ZMod S as a sum over range S
  have hsum : ∑ k : ZMod S, F.coeff k.val * G.coeff ((j : ZMod S) - k).val =
      ∑ a ∈ Finset.range S, F.coeff a * G.coeff ((j : ZMod S) - (a : ZMod S)).val := by
    refine Finset.sum_nbij' (fun k => k.val) (fun a => (a : ZMod S)) ?_ ?_ ?_ ?_ ?_
    · intro k _; simpa using ZMod.val_lt k
    · intro a _; simp
    · intro k _; simp
    · intro a ha; simp at ha; simp [ZMod.val_cast_of_lt ha]
    · intro k _; simp
  rw [hsum, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsplit : Finset.range S = Finset.range (j + 1) ∪ Finset.Ico (j + 1) S := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  rw [hsplit, Finset.sum_union (by
    rw [Finset.range_eq_Ico]; exact Finset.Ico_disjoint_Ico_consecutive _ _ _)]
  have hlow : ∀ a ∈ Finset.range (j + 1),
      F.coeff a * G.coeff ((j : ZMod S) - (a : ZMod S)).val = F.coeff a * G.coeff (j - a) := by
    intro a ha
    simp at ha
    rw [← Nat.cast_sub (by omega), ZMod.val_cast_of_lt (by omega)]
  have hhigh : ∀ a ∈ Finset.Ico (j + 1) S,
      F.coeff a * G.coeff ((j : ZMod S) - (a : ZMod S)).val = 0 := by
    intro a ha
    simp at ha
    by_cases hF : a ≤ F.natDegree
    · have e : (j : ZMod S) - (a : ZMod S) = ((S + j - a : ℕ) : ZMod S) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, zero_add]
      rw [e, ZMod.val_cast_of_lt (by omega)]
      rw [coeff_eq_zero_of_natDegree_lt (p := G) (by omega), mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh, Finset.sum_const_zero, add_zero]

theorem solution {d : ℕ} (s : Fin d → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (Function.onFun Nat.Coprime s)) {R : Type} [CommRing R] (F G : R[X])
    (hdeg : F.natDegree + G.natDegree < ∏ i, s i) (j : ℕ) (hj : j < ∏ i, s i) :
    (F * G).coeff j =
      ∑ b : Π i, ZMod (s i),
        F.coeff ((ZMod.prodEquivPi s hcop).symm b).val *
          G.coeff ((ZMod.prodEquivPi s hcop).symm (ZMod.prodEquivPi s hcop j - b)).val := by
  haveI : NeZero (∏ i, s i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (s i)⟩
  rw [cyclic_coeff_mul _ F G hdeg j hj]
  set e := ZMod.prodEquivPi s hcop
  refine (Fintype.sum_equiv e.toEquiv _ _ fun k => ?_)
  simp [map_sub]
