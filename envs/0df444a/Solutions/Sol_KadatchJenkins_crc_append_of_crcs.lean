-- Prove2me | solution 1 for KadatchJenkins.crc_append_of_crcs
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:10:30.805411+00:00
-- url     : https://prove2.me/submissions/ed216d54-c5b1-480a-9237-fc3c0515fb67

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

theorem crc_append_of_crcs (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree)
    (hu : u.degree < (P.natDegree : WithBot ℕ)) (M₁ M₂ : Message) (v v₁ v₂ : (ZMod 2)[X]) :
    let v₁' := crc P u M₁ v₁ + ((v - v₁) * X ^ M₁.length) % P
    let v₂' := crc P u M₂ v₂ + ((v₁' - v₂) * X ^ M₂.length) % P
    v₁' = crc P u M₁ v ∧ v₂' = crc P u M₂ v₁' ∧ crc P u (M₁ ++ M₂) v = v₂' := by
  intro v₁' v₂'
  have h1 : v₁' = crc P u M₁ v := (AuxKJ_ci P u hP hu M₁ v₁ v).symm
  have h2 : v₂' = crc P u M₂ v₁' := (AuxKJ_ci P u hP hu M₂ v₂ v₁').symm
  refine ⟨h1, h2, ?_⟩
  rw [h2, h1, AuxKJ_ap P u hP hu]

end KadatchJenkins

theorem solution (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree)
    (hu : u.degree < (P.natDegree : WithBot ℕ)) (M₁ M₂ : KadatchJenkins.Message) (v v₁ v₂ : (ZMod 2)[X]) :
    let v₁' := KadatchJenkins.crc P u M₁ v₁ + ((v - v₁) * X ^ M₁.length) % P
    let v₂' := KadatchJenkins.crc P u M₂ v₂ + ((v₁' - v₂) * X ^ M₂.length) % P
    v₁' = KadatchJenkins.crc P u M₁ v ∧ v₂' = KadatchJenkins.crc P u M₂ v₁' ∧ KadatchJenkins.crc P u (M₁ ++ M₂) v = v₂' :=
  KadatchJenkins.crc_append_of_crcs P u hP hu M₁ M₂ v v₁ v₂
