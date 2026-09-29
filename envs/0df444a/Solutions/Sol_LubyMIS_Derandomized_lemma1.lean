-- Prove2me | solution 1 for LubyMIS.Derandomized.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:44:41.403797+00:00
-- url     : https://prove2.me/submissions/5bb620e4-84e8-49fb-be83-12d74c9d288f

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_SampleSpace

namespace LubyMIS.Derandomized

/-- Shear map `(x, y) ↦ (x + y c, y)` on `ZMod q × ZMod q`. -/
def aux_l1_shear (q : ℕ) (c : ZMod q) : ZMod q × ZMod q ≃ ZMod q × ZMod q where
  toFun p := (p.1 + p.2 * c, p.2)
  invFun p := (p.1 - p.2 * c, p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem aux_l1_card (q : ℕ) [Fact q.Prime] (n : ℕ) {R : Type*} [DecidableEq R]
    (A : Fin n → ZMod q → R) (i : Fin n) (r : R) :
    (Finset.univ.filter (fun p : ZMod q × ZMod q => Xrv A i p = r)).card =
      nCount A i r * q := by
  have h := Finset.card_equiv (aux_l1_shear q ((i : ℕ) : ZMod q))
    (s := Finset.univ.filter (fun p : ZMod q × ZMod q => Xrv A i p = r))
    (t := (Finset.univ.filter (fun l => A i l = r)) ×ˢ (Finset.univ : Finset (ZMod q)))
    (by intro p; rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter]; simp [aux_l1_shear, Xrv])
  rw [h, Finset.card_product, Finset.card_univ, ZMod.card]
  rfl

end LubyMIS.Derandomized

open LubyMIS.Derandomized

theorem solution (q : ℕ) [Fact q.Prime] (n : ℕ) (hnq : n ≤ q) {R : Type*} [DecidableEq R]
    (A : Fin n → ZMod q → R) (i : Fin n) (r : R) :
    ((Finset.univ.filter (fun p : ZMod q × ZMod q => Xrv A i p = r)).card : ℝ) / (q : ℝ) ^ 2 =
      (nCount A i r : ℝ) / q := by
  rw [aux_l1_card q n A i r]
  have hq : (q : ℝ) ≠ 0 := by
    have := (Fact.out : q.Prime).pos
    positivity
  push_cast
  field_simp
