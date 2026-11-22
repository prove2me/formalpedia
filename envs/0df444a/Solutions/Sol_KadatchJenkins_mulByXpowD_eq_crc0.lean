-- Prove2me | solution 1 for KadatchJenkins.mulByXpowD_eq_crc0
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:06:53.142062+00:00
-- url     : https://prove2.me/submissions/a59857a4-e156-4e23-8127-313663944b59

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

theorem mulByXpowD_eq_crc0 (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (V : Message) :
    mulByXpowD P V.poly = crc0 P V 0 := by
  simp [mulByXpowD, crc0]

end KadatchJenkins

theorem solution (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (V : KadatchJenkins.Message) :
    KadatchJenkins.mulByXpowD P V.poly = KadatchJenkins.crc0 P V 0 :=
  KadatchJenkins.mulByXpowD_eq_crc0 P hP V
