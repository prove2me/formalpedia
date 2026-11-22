-- Prove2me | solution 1 for KadatchJenkins.stripeCrc_eq_crc0
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:13:31.876269+00:00
-- url     : https://prove2.me/submissions/c5ff8f91-a5ba-41e1-98ba-cc27422f6385

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

theorem AuxKJ_rep (k : ℕ) : Message.poly (List.replicate k (0 : ZMod 2)) = 0 := by
  induction k with
  | zero => simp [AuxKJ_poly_nil]
  | succ k ih => rw [List.replicate_succ, AuxKJ_poly_cons, ih]; try simp

theorem AuxKJ_c0app (P : (ZMod 2)[X]) (A B : Message) (v : (ZMod 2)[X]) :
    crc0 P (A ++ B) v = crc0 P B (crc0 P A v) := by
  unfold crc0
  rw [AuxKJ_mm, AuxKJ_poly_append, List.length_append]
  congr 1
  ring

theorem stripeCrc_eq_crc0 (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N : ℕ) (hN : 0 < N)
    (m : ℕ → ℕ → Message) (hm : ∀ k n, (m k n).length = W) (v : (ZMod 2)[X]) :
    (∀ k n, crc0 P (m k n ++ List.replicate ((N - 1) * W) 0) (stripeCrc P W N m v k n) =
        crcWordN P W N (m k n).poly (stripeCrc P W N m v k n)) ∧
      ∀ K n, 0 < K → stripeCrc P W N m v K n =
        crc0 P ((List.range K).flatMap fun k => m k n ++ List.replicate ((N - 1) * W) 0)
          (stripeCrc P W N m v 0 n) := by
  have h1 : ∀ k n, crc0 P (m k n ++ List.replicate ((N - 1) * W) 0) (stripeCrc P W N m v k n) =
      crcWordN P W N (m k n).poly (stripeCrc P W N m v k n) := by
    intro k n
    unfold crc0 crcWordN
    rw [AuxKJ_poly_append, AuxKJ_rep, List.length_append, List.length_replicate, hm]
    congr 1
    ring
  refine ⟨h1, ?_⟩
  intro K n hK
  induction K with
  | zero => omega
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h
      rw [show (List.range (0 + 1)).flatMap (fun k => m k n ++ List.replicate ((N - 1) * W) 0) =
        m 0 n ++ List.replicate ((N - 1) * W) 0 from by simp]
      rw [h1 0 n]
      rfl
    · rw [List.range_succ, List.flatMap_append, AuxKJ_c0app, ← ih h]
      rw [show [K].flatMap (fun k => m k n ++ List.replicate ((N - 1) * W) 0) =
        m K n ++ List.replicate ((N - 1) * W) 0 from by simp]
      rw [h1 K n]
      rfl

end KadatchJenkins

theorem solution (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N : ℕ) (hN : 0 < N)
    (m : ℕ → ℕ → KadatchJenkins.Message) (hm : ∀ k n, (m k n).length = W) (v : (ZMod 2)[X]) :
    (∀ k n, KadatchJenkins.crc0 P (m k n ++ List.replicate ((N - 1) * W) 0) (KadatchJenkins.stripeCrc P W N m v k n) =
        KadatchJenkins.crcWordN P W N (m k n).poly (KadatchJenkins.stripeCrc P W N m v k n)) ∧
      ∀ K n, 0 < K → KadatchJenkins.stripeCrc P W N m v K n =
        KadatchJenkins.crc0 P ((List.range K).flatMap fun k => m k n ++ List.replicate ((N - 1) * W) 0)
          (KadatchJenkins.stripeCrc P W N m v 0 n) :=
  KadatchJenkins.stripeCrc_eq_crc0 P hP W N hN m hm v
