-- Prove2me | solution 1 for KadatchJenkins.crc_replace
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:12:13.371837+00:00
-- url     : https://prove2.me/submissions/c8c755cd-d5e5-4625-8c3f-68a8b4f16ffd

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

theorem crc_replace (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (A B B' Cm : Message) (hB : B'.length = B.length) (v : (ZMod 2)[X]) :
    crc P u (A ++ B' ++ Cm) v =
        crc P u (A ++ B ++ Cm) v + ((B'.poly - B.poly) * X ^ (Cm.length + P.natDegree)) % P ∧
      crc P u B' v - crc P u B v = ((B'.poly - B.poly) * X ^ P.natDegree) % P ∧
      crc P u (A ++ B' ++ Cm) v =
        crc P u (A ++ B ++ Cm) v + ((crc P u B' v - crc P u B v) * X ^ Cm.length) % P := by
  have e1 : crc P u (A ++ B' ++ Cm) v =
      crc P u (A ++ B ++ Cm) v + ((B'.poly - B.poly) * X ^ (Cm.length + P.natDegree)) % P := by
    unfold crc
    rw [← Polynomial.add_mod]
    congr 1
    simp only [AuxKJ_poly_append, List.length_append, hB]
    ring
  have e2 : crc P u B' v - crc P u B v = ((B'.poly - B.poly) * X ^ P.natDegree) % P := by
    unfold crc
    rw [← Polynomial.sub_mod, hB]
    congr 1
    ring
  refine ⟨e1, e2, ?_⟩
  rw [e1, e2]
  congr 1
  have := AuxKJ_mm P ((B'.poly - B.poly) * X ^ P.natDegree) (X ^ Cm.length) 0
  simp only [add_zero] at this
  rw [this]
  congr 1
  ring

end KadatchJenkins

theorem solution (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (A B B' Cm : KadatchJenkins.Message) (hB : B'.length = B.length) (v : (ZMod 2)[X]) :
    KadatchJenkins.crc P u (A ++ B' ++ Cm) v =
        KadatchJenkins.crc P u (A ++ B ++ Cm) v + ((B'.poly - B.poly) * X ^ (Cm.length + P.natDegree)) % P ∧
      KadatchJenkins.crc P u B' v - KadatchJenkins.crc P u B v = ((B'.poly - B.poly) * X ^ P.natDegree) % P ∧
      KadatchJenkins.crc P u (A ++ B' ++ Cm) v =
        KadatchJenkins.crc P u (A ++ B ++ Cm) v + ((KadatchJenkins.crc P u B' v - KadatchJenkins.crc P u B v) * X ^ Cm.length) % P :=
  KadatchJenkins.crc_replace P u hP hu A B B' Cm hB v
