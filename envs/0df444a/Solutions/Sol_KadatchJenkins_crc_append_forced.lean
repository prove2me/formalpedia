-- Prove2me | solution 1 for KadatchJenkins.crc_append_forced
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:21:28.760552+00:00
-- url     : https://prove2.me/submissions/5634a4e3-c779-4269-8ee8-82f3dcb4e864

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

theorem AuxKJ_mm0 (P A B : (ZMod 2)[X]) : (A % P * B) % P = (A * B) % P := by
  simpa using AuxKJ_mm P A B 0

theorem crc_append_forced (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree)
    (hu : u.degree < (P.natDegree : WithBot ℕ)) (hX : ¬ X ∣ P) (W : ℕ) (hW : P.natDegree ≤ W)
    (M : Message) (v R : (ZMod 2)[X]) (hR : R.degree < (P.natDegree : WithBot ℕ)) :
    (∃ w : (ZMod 2)[X], (w * X ^ W) % P = 1) ∧
      ∀ w : (ZMod 2)[X], (w * X ^ W) % P = 1 →
        let Q := crc P u M v
        let q := ((R - u) * w - (Q - u)) % P
        crc P u (M ++ Message.ofPoly P.natDegree q ++ List.replicate (W - P.natDegree) 0) v = R ∧
          ∀ t : (ZMod 2)[X], t.degree < (P.natDegree : WithBot ℕ) →
            crc P u (M ++ Message.ofPoly P.natDegree t ++ List.replicate (W - P.natDegree) 0) v = R → t = q := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have h1P : (1 : (ZMod 2)[X]) % P = 1 := by
    rw [Polynomial.mod_eq_self_iff hP0, degree_one, degree_eq_natDegree hP0]
    exact_mod_cast hP
  have hred : ∀ A : (ZMod 2)[X], A.degree < (P.natDegree : WithBot ℕ) → A % P = A := fun A hA => by
    rw [Polynomial.mod_eq_self_iff hP0, degree_eq_natDegree hP0]; exact hA
  have hdm : ∀ A : (ZMod 2)[X], (A % P).degree < (P.natDegree : WithBot ℕ) := fun A => by
    rw [← degree_eq_natDegree hP0]; exact Polynomial.degree_mod_lt _ hP0
  have hX' : (X : (ZMod 2)[X]) ^ W = X ^ P.natDegree * X ^ (W - P.natDegree) := by
    rw [← pow_add]; congr 1; omega
  -- formula for appended CRC
  have F : ∀ t : (ZMod 2)[X], t.degree < (P.natDegree : WithBot ℕ) →
      crc P u (M ++ Message.ofPoly P.natDegree t ++ List.replicate (W - P.natDegree) 0) v =
        ((crc P u M v - u + t) * X ^ W + u) % P := by
    intro t ht
    have e1 : (M ++ Message.ofPoly P.natDegree t ++ List.replicate (W - P.natDegree) 0).poly =
        M.poly * X ^ W + t * X ^ (W - P.natDegree) := by
      rw [AuxKJ_poly_append, AuxKJ_poly_append, AuxKJ_rep, AuxKJ_ofPoly _ _ ht, List.length_replicate,
        AuxKJ_ofPoly_len, hX']
      ring
    have hlen : (M ++ Message.ofPoly P.natDegree t ++ List.replicate (W - P.natDegree) 0).length
        = M.length + W := by
      simp [AuxKJ_ofPoly_len]; omega
    conv_lhs => unfold crc
    rw [e1, hlen]
    have key : (crc P u M v - u + t) * X ^ W + u = crc P u M v * X ^ W + ((t - u) * X ^ W + u) := by ring
    rw [key]
    unfold crc
    rw [AuxKJ_mm]
    congr 1
    simp only [pow_add, hX']
    ring
  have hmul1 : ∀ w A : (ZMod 2)[X], (w * X ^ W) % P = 1 → (A * (w * X ^ W)) % P = A % P := by
    intro w A hw
    rw [Polynomial.mul_mod, hw, mul_one]
    exact (Polynomial.mod_eq_self_iff hP0).mpr (Polynomial.degree_mod_lt _ hP0)
  refine ⟨?_, ?_⟩
  · have hirr : Irreducible (X : (ZMod 2)[X]) := Polynomial.irreducible_X
    have hcop : IsCoprime (X : (ZMod 2)[X]) P := (Irreducible.coprime_iff_not_dvd hirr).mpr hX
    obtain ⟨a, b, hab⟩ := (hcop.pow_left : IsCoprime ((X : (ZMod 2)[X]) ^ W) P)
    refine ⟨a, ?_⟩
    have : a * X ^ W = 1 - b * P := by rw [← hab]; ring
    rw [this, Polynomial.sub_mod, EuclideanDomain.mod_eq_zero.mpr (dvd_mul_left P b), sub_zero, h1P]
  intro w hw Q q
  refine ⟨?_, ?_⟩
  · rw [F q (hdm _)]
    have : (Q - u + q) * X ^ W + u = q * X ^ W + ((Q - u) * X ^ W + u) := by ring
    show ((Q - u + q) * X ^ W + u) % P = R
    rw [this, AuxKJ_mm]
    have : ((R - u) * w - (Q - u)) * X ^ W + ((Q - u) * X ^ W + u) = (R - u) * (w * X ^ W) + u := by ring
    rw [this, Polynomial.add_mod, hmul1 w _ hw, ← Polynomial.add_mod, sub_add_cancel, hred R hR]
  · intro t ht h
    rw [F t ht] at h
    change ((Q - u + t) * X ^ W + u) % P = R at h
    have hY : ((Q - u + t) * X ^ W) % P = R - u := by
      rw [Polynomial.add_mod, hred u hu] at h
      rw [← h]; ring
    have h2 : (Q - u + t) % P = (w * (R - u)) % P := by
      rw [← hmul1 w _ hw]
      have : (Q - u + t) * (w * X ^ W) = w * ((Q - u + t) * X ^ W) := by ring
      rw [this, Polynomial.mul_mod, hY]
      exact AuxKJ_mm0 P w (R - u)
    rw [← hred t ht]
    show t % P = ((R - u) * w - (Q - u)) % P
    have : t = (Q - u + t) - (Q - u) := by ring
    rw [this, Polynomial.sub_mod, h2, ← Polynomial.sub_mod]
    congr 1
    ring

end KadatchJenkins

theorem solution (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree)
    (hu : u.degree < (P.natDegree : WithBot ℕ)) (hX : ¬ X ∣ P) (W : ℕ) (hW : P.natDegree ≤ W)
    (M : KadatchJenkins.Message) (v R : (ZMod 2)[X]) (hR : R.degree < (P.natDegree : WithBot ℕ)) :
    (∃ w : (ZMod 2)[X], (w * X ^ W) % P = 1) ∧
      ∀ w : (ZMod 2)[X], (w * X ^ W) % P = 1 →
        let Q := KadatchJenkins.crc P u M v
        let q := ((R - u) * w - (Q - u)) % P
        KadatchJenkins.crc P u (M ++ KadatchJenkins.Message.ofPoly P.natDegree q ++ List.replicate (W - P.natDegree) 0) v = R ∧
          ∀ t : (ZMod 2)[X], t.degree < (P.natDegree : WithBot ℕ) →
            KadatchJenkins.crc P u (M ++ KadatchJenkins.Message.ofPoly P.natDegree t ++ List.replicate (W - P.natDegree) 0) v = R → t = q :=
  KadatchJenkins.crc_append_forced P u hP hu hX W hW M v R hR
