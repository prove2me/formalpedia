-- Prove2me | solution 1 for KadatchJenkins.crc_eq_crc0_add
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:10:47.665216+00:00
-- url     : https://prove2.me/submissions/17246263-8434-4ccd-834f-2a05523fbced

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial
namespace KadatchJenkins

theorem AuxKJ_poly_nil : Message.poly [] = 0 := by simp [Message.poly]

theorem AuxKJ_poly_cons (a : ZMod 2) (M : Message) :
    Message.poly (a :: M) = C a * X ^ M.length + M.poly := by
  unfold Message.poly
  refine (Fin.sum_univ_succ (n := M.length)
    (f := fun k : Fin (M.length + 1) => C ((a :: M).get k) * X ^ (M.length + 1 - 1 - (k : ℕ)))).trans ?_
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 2
  simp only [Fin.val_succ]
  omega

theorem AuxKJ_poly_append (M₁ M₂ : Message) :
    (M₁ ++ M₂).poly = M₁.poly * X ^ M₂.length + M₂.poly := by
  induction M₁ with
  | nil => simp [AuxKJ_poly_nil]
  | cons a M ih =>
    rw [List.cons_append, AuxKJ_poly_cons, AuxKJ_poly_cons, ih, List.length_append]
    ring

theorem AuxKJ_mm (P A B C : (ZMod 2)[X]) : (A % P * B + C) % P = (A * B + C) % P := by
  rw [EuclideanDomain.mod_eq_sub_mul_div A P]
  have : (A - P * (A / P)) * B + C = (A * B + C) - P * ((A / P) * B) := by ring
  rw [this, Polynomial.sub_mod, EuclideanDomain.mod_eq_zero.mpr (dvd_mul_right _ _), sub_zero]

theorem AuxKJ_ci (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (M : Message) (v v' : (ZMod 2)[X]) :
    crc P u M v' = crc P u M v + ((v' - v) * X ^ M.length) % P := by
  unfold crc
  rw [← Polynomial.add_mod]
  congr 1
  ring

theorem AuxKJ_ap (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (M₁ M₂ : Message) (v : (ZMod 2)[X]) :
    crc P u (M₁ ++ M₂) v = crc P u M₂ (crc P u M₁ v) := by
  unfold crc
  rw [show ∀ Q : (ZMod 2)[X], (Q - u) * X ^ M₂.length + M₂.poly * X ^ P.natDegree + u =
      Q * X ^ M₂.length + (M₂.poly * X ^ P.natDegree + u - u * X ^ M₂.length) from fun Q => by ring,
    AuxKJ_mm, AuxKJ_poly_append, List.length_append]
  congr 1
  ring

theorem AuxKJ_umod (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ)) :
    u % P = u := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  rw [Polynomial.mod_eq_self_iff hP0, Polynomial.degree_eq_natDegree hP0]; exact hu

theorem crc_eq_crc0_add (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (v : (ZMod 2)[X]) :
    (∀ M : Message, crc P u M v = crc0 P M (v - u) + u) ∧
      ∀ Ms : List Message, Ms ≠ [] → crc P u Ms.flatten v = Ms.foldl (fun w Mk => crc0 P Mk w) (v - u) + u := by
  have h1 : ∀ (v : (ZMod 2)[X]) (M : Message), crc P u M v = crc0 P M (v - u) + u := by
    intro v M
    unfold crc crc0
    rw [Polynomial.add_mod _ u, AuxKJ_umod P u hP hu]
  refine ⟨h1 v, ?_⟩
  intro Ms hMs
  induction Ms generalizing v with
  | nil => exact absurd rfl hMs
  | cons M rest ih =>
    rcases eq_or_ne rest [] with h | h
    · subst h; simp [h1]
    · rw [List.flatten_cons, AuxKJ_ap P u hP hu, ih _ h, List.foldl_cons, h1 v M, add_sub_cancel_right]

end KadatchJenkins

theorem solution (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (v : (ZMod 2)[X]) :
    (∀ M : KadatchJenkins.Message, KadatchJenkins.crc P u M v = KadatchJenkins.crc0 P M (v - u) + u) ∧
      ∀ Ms : List KadatchJenkins.Message, Ms ≠ [] → KadatchJenkins.crc P u Ms.flatten v = Ms.foldl (fun w Mk => KadatchJenkins.crc0 P Mk w) (v - u) + u :=
  KadatchJenkins.crc_eq_crc0_add P u hP hu v
