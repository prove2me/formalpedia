-- Prove2me | solution 1 for KadatchJenkins.crc0_eq_sum_stripeCrc_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:19:54.086953+00:00
-- url     : https://prove2.me/submissions/2592e580-6827-4d07-ac6c-4a132899fbb6

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

theorem AuxKJ_G (L : ℕ) (f : ℕ → Message) (hf : ∀ i, (f i).length = L) (n : ℕ) :
    Message.poly ((List.range n).flatMap f) = ∑ i ∈ Finset.range n, (f i).poly * X ^ ((n - 1 - i) * L) ∧
    ((List.range n).flatMap f).length = n * L := by
  induction n with
  | zero => simp [AuxKJ_poly_nil]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [List.range_succ, List.flatMap_append]
    have hs : [n].flatMap f = f n := by simp
    rw [hs, AuxKJ_poly_append, ih1, List.length_append, ih2, hf, Finset.sum_range_succ, Finset.sum_mul]
    refine ⟨?_, by rw [Nat.succ_mul]⟩
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' := Finset.mem_range.mp hi
      rw [mul_assoc, ← pow_add]
      congr 2
      rw [show n + 1 - 1 - i = (n - 1 - i) + 1 by omega, Nat.add_mul, one_mul]
    · simp

theorem AuxKJ_c0app (P : (ZMod 2)[X]) (A B : Message) (v : (ZMod 2)[X]) :
    crc0 P (A ++ B) v = crc0 P B (crc0 P A v) := by
  unfold crc0
  rw [AuxKJ_mm, AuxKJ_poly_append, List.length_append]
  congr 1
  ring

theorem AuxKJ_mm0 (P A B : (ZMod 2)[X]) : (A % P * B) % P = (A * B) % P := by
  simpa using AuxKJ_mm P A B 0

theorem AuxKJ_re (P T Y Z Cg : (ZMod 2)[X]) : (Z * (T * Y + Cg)) % P = (T * (Z * Y) + Z * Cg) % P := by
  congr 1; ring

theorem AuxKJ_summod (P : (ZMod 2)[X]) (a b : ℕ → (ZMod 2)[X]) (n : ℕ) :
    (∑ i ∈ Finset.range n, a i % P * b i) % P = (∑ i ∈ Finset.range n, a i * b i) % P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Polynomial.add_mod, ih, ← Polynomial.add_mod]
    rw [add_comm, AuxKJ_mm, add_comm]

theorem AuxKJ_summod' (P : (ZMod 2)[X]) (a b : ℕ → (ZMod 2)[X]) (n : ℕ) :
    (∑ i ∈ Finset.range n, a i * (b i % P)) % P = (∑ i ∈ Finset.range n, a i * b i) % P := by
  simp_rw [mul_comm (a _)]
  exact AuxKJ_summod P b a n

theorem crc0_eq_sum_stripeCrc_mul_inv (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N K : ℕ)
    (hN : 0 < N) (m : ℕ → ℕ → Message) (hm : ∀ k n, (m k n).length = W) (v : (ZMod 2)[X]) :
    ((∃ w : (ZMod 2)[X], (w * X ^ W) % P = 1) ↔ (¬ X ∣ P ∨ W = 0)) ∧
      ∀ w : (ZMod 2)[X], (w * X ^ W) % P = 1 →
        crc0 P ((List.range K).flatMap fun k => (List.range N).flatMap fun n => m k n) v =
          (∑ n ∈ Finset.range N, stripeCrc P W N m v K n * w ^ n) % P := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have h1P : (1 : (ZMod 2)[X]) % P = 1 := by
    rw [Polynomial.mod_eq_self_iff hP0, degree_one, degree_eq_natDegree hP0]
    exact_mod_cast hP
  have hmodmod : ∀ A : (ZMod 2)[X], A % P % P = A % P := fun A => by
    rw [Polynomial.mod_eq_self_iff hP0]; exact Polynomial.degree_mod_lt _ hP0
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨w, hw⟩
    by_contra hc
    push_neg at hc
    obtain ⟨hXP, hW⟩ := hc
    have e := EuclideanDomain.mod_add_div (w * X ^ W) P
    rw [hw] at e
    have h1 : X ∣ w * X ^ W := Dvd.dvd.mul_left (dvd_pow_self X hW) w
    have h2 : X ∣ P * (w * X ^ W / P) := Dvd.dvd.mul_right hXP _
    have h3 : (X : (ZMod 2)[X]) ∣ 1 := by
      have : (1 : (ZMod 2)[X]) = w * X ^ W - P * (w * X ^ W / P) := by linear_combination e
      rw [this]; exact dvd_sub h1 h2
    have := Polynomial.natDegree_le_of_dvd h3 one_ne_zero
    simp at this
  · rintro (h | h)
    · have hirr : Irreducible (X : (ZMod 2)[X]) := Polynomial.irreducible_X
      have hcop : IsCoprime (X : (ZMod 2)[X]) P := (Irreducible.coprime_iff_not_dvd hirr).mpr h
      obtain ⟨a, b, hab⟩ := (hcop.pow_left : IsCoprime ((X : (ZMod 2)[X]) ^ W) P)
      refine ⟨a, ?_⟩
      have : a * X ^ W = 1 - b * P := by rw [← hab]; ring
      rw [this, Polynomial.sub_mod, EuclideanDomain.mod_eq_zero.mpr (dvd_mul_left P b), sub_zero, h1P]
    · exact ⟨1, by rw [h, pow_zero, mul_one, h1P]⟩
  intro w hw
  set G : ℕ → Message := fun k => (List.range N).flatMap fun n => m k n with hG
  set s := stripeCrc P W N m v with hs
  have hGp : ∀ k, (G k).poly = ∑ n ∈ Finset.range N, (m k n).poly * X ^ ((N - 1 - n) * W) :=
    fun k => (AuxKJ_G W (m k) (hm k) N).1
  have hGl : ∀ k, (G k).length = N * W := fun k => (AuxKJ_G W (m k) (hm k) N).2
  have hXN : (X : (ZMod 2)[X]) ^ ((N - 1) * W) * X ^ W = X ^ (N * W) := by
    rw [← pow_add]; congr 1
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    simp [Nat.add_mul]
  have hsucc : ∀ K, crc0 P ((List.range (K + 1)).flatMap G) v
      = (crc0 P ((List.range K).flatMap G) v * X ^ (N * W) + (G K).poly * X ^ P.natDegree) % P := by
    intro K
    rw [List.range_succ, List.flatMap_append, AuxKJ_c0app]
    rw [show [K].flatMap G = G K from by simp]
    unfold crc0
    rw [hGl K]
  -- the sum expression
  have hsum : ∀ K, (∑ n ∈ Finset.range N, ((s K n * X ^ W + (m K n).poly * X ^ P.natDegree) *
          X ^ ((N - 1 - n) * W))) = (∑ n ∈ Finset.range N, s K n * X ^ ((N - 1 - n) * W)) * X ^ W
          + (G K).poly * X ^ P.natDegree := by
    intro K
    rw [hGp, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  have inv : ∀ K, (∑ n ∈ Finset.range N, s K n * X ^ ((N - 1 - n) * W)) % P
      = (crc0 P ((List.range K).flatMap G) v * X ^ ((N - 1) * W)) % P := by
    intro K
    induction K with
    | zero =>
      simp only [List.range_zero, List.flatMap_nil]
      rw [Finset.sum_eq_single 0]
      · simp [hs, stripeCrc, crc0, AuxKJ_poly_nil]
        rw [AuxKJ_mm0]
      · intro b _ hb; simp [hs, stripeCrc, hb]
      · intro h; exact absurd (Finset.mem_range.mpr hN) h
    | succ K ih =>
      have e1 : ∀ n, s (K + 1) n = ((s K n * X ^ W + (m K n).poly * X ^ P.natDegree) * X ^ ((N - 1) * W)) % P := by
        intro n; simp only [hs, stripeCrc, crcWordN]
      simp_rw [e1]
      rw [AuxKJ_summod, hsucc]
      have : (∑ n ∈ Finset.range N, (s K n * X ^ W + (m K n).poly * X ^ P.natDegree) * X ^ ((N - 1) * W) *
          X ^ ((N - 1 - n) * W)) = X ^ ((N - 1) * W) * (∑ n ∈ Finset.range N, ((s K n * X ^ W + (m K n).poly * X ^ P.natDegree) *
          X ^ ((N - 1 - n) * W))) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => ?_); ring
      rw [this, hsum, AuxKJ_mm0, AuxKJ_re, ← AuxKJ_mm, ih, AuxKJ_mm, hXN]
      congr 1
      ring
  have hupow : ∀ k : ℕ, (w * X ^ W) ^ k % P = 1 := by
    intro k
    induction k with
    | zero => rw [pow_zero, h1P]
    | succ k ih => rw [pow_succ, Polynomial.mul_mod, ih, hw, one_mul, h1P]
  have hred : crc0 P ((List.range K).flatMap G) v % P = crc0 P ((List.range K).flatMap G) v := by
    unfold crc0; exact hmodmod _
  show crc0 P ((List.range K).flatMap G) v = _
  calc crc0 P ((List.range K).flatMap G) v
      = (crc0 P ((List.range K).flatMap G) v * ((w * X ^ W) ^ (N - 1) % P)) % P := by
        rw [hupow, mul_one, hred]
    _ = ((crc0 P ((List.range K).flatMap G) v * X ^ ((N - 1) * W)) * w ^ (N - 1)) % P := by
        rw [mul_comm _ (_ % P), AuxKJ_mm0]
        refine congrArg (· % P) ?_
        rw [mul_pow, ← pow_mul, mul_comm W (N - 1)]; ring
    _ = ((∑ n ∈ Finset.range N, s K n * X ^ ((N - 1 - n) * W)) * w ^ (N - 1)) % P := by
        rw [← AuxKJ_mm0, ← inv K, AuxKJ_mm0]
    _ = (∑ n ∈ Finset.range N, s K n * w ^ n * (w * X ^ W) ^ (N - 1 - n)) % P := by
        rw [Finset.sum_mul]
        refine congrArg (· % P) (Finset.sum_congr rfl (fun n hn => ?_))
        have hn' := Finset.mem_range.mp hn
        obtain ⟨j, hj⟩ : ∃ j, N - 1 = n + j := ⟨N - 1 - n, by omega⟩
        rw [hj, Nat.add_sub_cancel_left, pow_add, mul_pow, ← pow_mul, mul_comm j W]
        ring
    _ = (∑ n ∈ Finset.range N, s K n * w ^ n) % P := by
        rw [← AuxKJ_summod']
        simp only [hupow, mul_one]

end KadatchJenkins

theorem solution (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N K : ℕ)
    (hN : 0 < N) (m : ℕ → ℕ → KadatchJenkins.Message) (hm : ∀ k n, (m k n).length = W) (v : (ZMod 2)[X]) :
    ((∃ w : (ZMod 2)[X], (w * X ^ W) % P = 1) ↔ (¬ X ∣ P ∨ W = 0)) ∧
      ∀ w : (ZMod 2)[X], (w * X ^ W) % P = 1 →
        KadatchJenkins.crc0 P ((List.range K).flatMap fun k => (List.range N).flatMap fun n => m k n) v =
          (∑ n ∈ Finset.range N, KadatchJenkins.stripeCrc P W N m v K n * w ^ n) % P :=
  KadatchJenkins.crc0_eq_sum_stripeCrc_mul_inv P hP W N K hN m hm v
