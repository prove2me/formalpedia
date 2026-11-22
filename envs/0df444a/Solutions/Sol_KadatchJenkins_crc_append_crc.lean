-- Prove2me | solution 1 for KadatchJenkins.crc_append_crc
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:12:58.299807+00:00
-- url     : https://prove2.me/submissions/e9157759-739b-47a2-b2e6-4216f1b881cf

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

theorem AuxKJ_ofPoly_len (n : ℕ) (p : (ZMod 2)[X]) : (Message.ofPoly n p).length = n := by
  simp [Message.ofPoly]

theorem AuxKJ_ofPoly_sum (n : ℕ) (p : (ZMod 2)[X]) :
    (Message.ofPoly n p).poly = ∑ i ∈ Finset.range n, C (p.coeff i) * X ^ i := by
  induction n with
  | zero => simp [Message.ofPoly, AuxKJ_poly_nil]
  | succ n ih =>
    have h : Message.ofPoly (n + 1) p = p.coeff n :: Message.ofPoly n p := by
      unfold Message.ofPoly
      rw [List.ofFn_succ]
      congr 1
      refine congrArg List.ofFn (funext fun k => ?_)
      simp only [Fin.val_succ]
      congr 1
      omega
    rw [h, AuxKJ_poly_cons, ih, AuxKJ_ofPoly_len, Finset.sum_range_succ, add_comm]

theorem AuxKJ_ofPoly (n : ℕ) (p : (ZMod 2)[X]) (hp : p.degree < (n : WithBot ℕ)) :
    (Message.ofPoly n p).poly = p := by
  by_cases h0 : p = 0
  · subst h0; rw [AuxKJ_ofPoly_sum]; simp
  rw [AuxKJ_ofPoly_sum]
  conv_rhs => rw [p.as_sum_range' n (by rw [degree_eq_natDegree h0] at hp; exact_mod_cast hp)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [C_mul_X_pow_eq_monomial]

theorem AuxKJ_rep (k : ℕ) : Message.poly (List.replicate k (0 : ZMod 2)) = 0 := by
  induction k with
  | zero => simp [AuxKJ_poly_nil]
  | succ k ih => rw [List.replicate_succ, AuxKJ_poly_cons, ih]; try simp

theorem AuxKJ_two : (2 : (ZMod 2)[X]) = 0 := by
  exact_mod_cast CharP.cast_eq_zero (ZMod 2)[X] 2

theorem crc_append_crc (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (W : ℕ) (hW : P.natDegree ≤ W) (M : Message) (v : (ZMod 2)[X]) :
    (M ++ Message.ofPoly P.natDegree (crc P u M v) ++ List.replicate (W - P.natDegree) 0).poly =
        M.poly * X ^ W + crc P u M v * X ^ (W - P.natDegree) ∧
      crc P u (M ++ Message.ofPoly P.natDegree (crc P u M v) ++ List.replicate (W - P.natDegree) 0) v =
        (u * (1 - X ^ W)) % P := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have hc : (crc P u M v).degree < (P.natDegree : WithBot ℕ) := by
    unfold crc; rw [← degree_eq_natDegree hP0]; exact Polynomial.degree_mod_lt _ hP0
  set c := crc P u M v with hcd
  have hX : (X : (ZMod 2)[X]) ^ W = X ^ P.natDegree * X ^ (W - P.natDegree) := by
    rw [← pow_add]; congr 1; omega
  have e1 : (M ++ Message.ofPoly P.natDegree (crc P u M v) ++ List.replicate (W - P.natDegree) 0).poly =
      M.poly * X ^ W + crc P u M v * X ^ (W - P.natDegree) := by
    rw [AuxKJ_poly_append, AuxKJ_poly_append, AuxKJ_rep, AuxKJ_ofPoly _ _ hc, List.length_replicate,
      AuxKJ_ofPoly_len, hX]
    ring
  refine ⟨e1, ?_⟩
  have hlen : (M ++ Message.ofPoly P.natDegree (crc P u M v) ++ List.replicate (W - P.natDegree) 0).length
      = M.length + W := by
    simp [AuxKJ_ofPoly_len]; omega
  conv_lhs => unfold crc
  rw [e1, hlen]
  have key : ((v - u) * X ^ (M.length + W) + (M.poly * X ^ W + crc P u M v * X ^ (W - P.natDegree)) * X ^ P.natDegree + u)
      = crc P u M v * X ^ W + ((v - u) * X ^ (M.length + W) + M.poly * X ^ W * X ^ P.natDegree + u) := by
    rw [hX]; ring
  rw [key]
  unfold crc
  rw [AuxKJ_mm]
  congr 1
  linear_combination (((v - u) * X ^ M.length + M.poly * X ^ P.natDegree) * X ^ W + u * X ^ W) * AuxKJ_two

end KadatchJenkins

theorem solution (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (W : ℕ) (hW : P.natDegree ≤ W) (M : KadatchJenkins.Message) (v : (ZMod 2)[X]) :
    (M ++ KadatchJenkins.Message.ofPoly P.natDegree (KadatchJenkins.crc P u M v) ++ List.replicate (W - P.natDegree) 0).poly =
        M.poly * X ^ W + KadatchJenkins.crc P u M v * X ^ (W - P.natDegree) ∧
      KadatchJenkins.crc P u (M ++ KadatchJenkins.Message.ofPoly P.natDegree (KadatchJenkins.crc P u M v) ++ List.replicate (W - P.natDegree) 0) v =
        (u * (1 - X ^ W)) % P :=
  KadatchJenkins.crc_append_crc P u hP hu W hW M v
