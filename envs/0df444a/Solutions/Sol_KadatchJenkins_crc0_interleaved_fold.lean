-- Prove2me | solution 1 for KadatchJenkins.crc0_interleaved_fold
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:16:00.856817+00:00
-- url     : https://prove2.me/submissions/638436df-6a76-413f-b96a-dcfd1f64a118

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

theorem crc0_interleaved_fold (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N K : ℕ) (hN : 0 < N)
    (m : ℕ → ℕ → Message) (hm : ∀ k n, (m k n).length = W) (v : (ZMod 2)[X]) :
    (List.range N).foldl (fun v' n => crc0 P (m K n) (v' + stripeCrc P W N m v K n)) 0 =
      (∑ n ∈ Finset.range N, crc0 P (m K n) (stripeCrc P W N m v K n) * X ^ ((N - 1 - n) * W)) % P := by
  set s := stripeCrc P W N m v K with hs
  have key : ∀ j, (List.range j).foldl (fun v' n => crc0 P (m K n) (v' + s n)) 0 =
      (∑ n ∈ Finset.range j, crc0 P (m K n) (s n) * X ^ ((j - 1 - n) * W)) % P := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
      have hc : crc0 P (m K j) (s j) % P = crc0 P (m K j) (s j) := by
        have hP0 : P ≠ 0 := by rintro rfl; simp at hP
        unfold crc0; rw [Polynomial.mod_eq_self_iff hP0]; exact Polynomial.degree_mod_lt _ hP0
      have e : crc0 P (m K j) ((∑ n ∈ Finset.range j, crc0 P (m K n) (s n) * X ^ ((j - 1 - n) * W)) % P + s j)
          = ((∑ n ∈ Finset.range j, crc0 P (m K n) (s n) * X ^ ((j - 1 - n) * W)) % P * X ^ W
              + (s j * X ^ W + (m K j).poly * X ^ P.natDegree)) % P := by
        unfold crc0; rw [hm]; congr 1; ring
      rw [e, AuxKJ_mm, Finset.sum_range_succ, Finset.sum_mul]
      rw [Polynomial.add_mod, Polynomial.add_mod (∑ x ∈ Finset.range j, _)]
      congr 1
      · congr 1
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' := Finset.mem_range.mp hi
        rw [mul_assoc, ← pow_add]
        congr 2
        rw [show j + 1 - 1 - i = (j - 1 - i) + 1 by omega, Nat.add_mul, one_mul]
      · simp only [Nat.add_sub_cancel, Nat.sub_self, zero_mul, pow_zero, mul_one]
        rw [hc]
        unfold crc0
        rw [hm]
  exact key N

end KadatchJenkins

theorem solution (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N K : ℕ) (hN : 0 < N)
    (m : ℕ → ℕ → KadatchJenkins.Message) (hm : ∀ k n, (m k n).length = W) (v : (ZMod 2)[X]) :
    (List.range N).foldl (fun v' n => KadatchJenkins.crc0 P (m K n) (v' + KadatchJenkins.stripeCrc P W N m v K n)) 0 =
      (∑ n ∈ Finset.range N, KadatchJenkins.crc0 P (m K n) (KadatchJenkins.stripeCrc P W N m v K n) * X ^ ((N - 1 - n) * W)) % P :=
  KadatchJenkins.crc0_interleaved_fold P hP W N K hN m hm v
