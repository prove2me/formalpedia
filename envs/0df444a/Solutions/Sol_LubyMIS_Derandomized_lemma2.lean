-- Prove2me | solution 1 for LubyMIS.Derandomized.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:37:28.325742+00:00
-- url     : https://prove2.me/submissions/9595c5fd-8320-420d-8c9b-72dac59af73d

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_SampleSpace

namespace LubyMIS.Derandomized

theorem aux_lmd2_card (q : ℕ) [Fact q.Prime] (n : ℕ) (hnq : n ≤ q) {R : Type*} [DecidableEq R]
    (A : Fin n → ZMod q → R) (i i' : Fin n) (hii' : i ≠ i') (r r' : R) :
    (Finset.univ.filter (fun p : ZMod q × ZMod q => Xrv A i p = r ∧ Xrv A i' p = r')).card =
      nCount A i r * nCount A i' r' := by
  set a : ZMod q := ((i : ℕ) : ZMod q) with ha
  set b : ZMod q := ((i' : ℕ) : ZMod q) with hb
  have hab : a - b ≠ 0 := by
    intro h
    have h' : a = b := sub_eq_zero.mp h
    rw [ha, hb, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hnq),
      Nat.mod_eq_of_lt (lt_of_lt_of_le i'.isLt hnq)] at h'
    exact hii' (Fin.ext h')
  unfold nCount
  rw [← Finset.card_product]
  apply Finset.card_bij' (fun p _ => (p.1 + p.2 * a, p.1 + p.2 * b))
    (fun u _ => (u.1 - (u.1 - u.2) / (a - b) * a, (u.1 - u.2) / (a - b)))
  · intro p hp
    rw [Finset.mem_filter] at hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp.2
  · intro u hu
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have e1 : u.1 - (u.1 - u.2) / (a - b) * a + (u.1 - u.2) / (a - b) * a = u.1 := by ring
    have e2 : u.1 - (u.1 - u.2) / (a - b) * a + (u.1 - u.2) / (a - b) * b = u.2 := by
      field_simp
      ring
    show A i (_ + _ * a) = r ∧ A i' (_ + _ * b) = r'
    rw [e1, e2]
    exact hu
  · intro p _
    ext
    · simp only
      have : (p.1 + p.2 * a - (p.1 + p.2 * b)) / (a - b) = p.2 := by
        field_simp
        ring
      rw [this]; ring
    · simp only
      field_simp
      ring
  · intro u _
    ext
    · simp only
      ring
    · simp only
      field_simp
      ring

end LubyMIS.Derandomized

open LubyMIS.Derandomized

theorem solution (q : ℕ) [Fact q.Prime] (n : ℕ) (hnq : n ≤ q) {R : Type*} [DecidableEq R]
    (A : Fin n → ZMod q → R) (i i' : Fin n) (hii' : i ≠ i') (r r' : R) :
    ((Finset.univ.filter (fun p : ZMod q × ZMod q => Xrv A i p = r ∧ Xrv A i' p = r')).card : ℝ) /
        (q : ℝ) ^ 2 =
      ((nCount A i r : ℝ) * (nCount A i' r' : ℝ)) / (q : ℝ) ^ 2 := by
  rw [aux_lmd2_card q n hnq A i i' hii' r r', Nat.cast_mul]
