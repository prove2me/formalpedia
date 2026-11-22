-- Prove2me | solution 1 for KadatchJenkins.crc_roll
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T09:06:14.86436+00:00
-- url     : https://prove2.me/submissions/34c0ff69-440e-43b0-bc2f-d2eb8bea313d

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

theorem AuxKJ_msg (W N : ℕ) (m : ℕ → Message) (hm : ∀ k, (m k).length = W) (j : ℕ) :
    Message.poly ((List.range N).flatMap fun n => m (j + n)) =
      ∑ i ∈ Finset.range N, (m (j + i)).poly * X ^ ((N - 1 - i) * W) ∧
    ((List.range N).flatMap fun n => m (j + n)).length = N * W :=
  AuxKJ_G W (fun n => m (j + n)) (fun i => hm _) N

theorem crc_roll (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (W N : ℕ) (m : ℕ → Message) (hm : ∀ k, (m k).length = W) (v : (ZMod 2)[X]) (k : ℕ) :
    let Msg : ℕ → Message := fun j => (List.range N).flatMap fun n => m (j + n)
    let F := (crc P u (Msg k) v * X ^ W + (m (k + N)).poly * X ^ P.natDegree) % P
    let G := (((v - u) * X ^ (N * W) + u) * (1 - X ^ W) -
      (m k).poly * X ^ (P.natDegree + N * W)) % P
    (Msg (k + 1)).poly = (Msg k).poly * X ^ W - (m k).poly * X ^ (N * W) + (m (k + N)).poly ∧
    crc P u (Msg (k + 1)) v = ((v - u) * X ^ (N * W) + u +
        ∑ n ∈ Finset.range N, (m (k + 1 + n)).poly * X ^ (P.natDegree + W * (N - 1 - n))) % P ∧
      crc P u (Msg (k + 1)) v = F + G ∧ F.degree < (P.natDegree : WithBot ℕ) ∧ G.degree < (P.natDegree : WithBot ℕ) := by
  intro Msg F G
  have hP0 : P ≠ 0 := by
    rintro rfl; simp at hP
  have hdeg : ∀ A : (ZMod 2)[X], (A % P).degree < (P.natDegree : WithBot ℕ) := by
    intro A
    rw [← Polynomial.degree_eq_natDegree hP0]
    exact Polynomial.degree_mod_lt _ hP0
  have e1 : (Msg (k + 1)).poly = (Msg k).poly * X ^ W - (m k).poly * X ^ (N * W) + (m (k + N)).poly := by
    simp only [Msg]
    rw [(AuxKJ_msg W N m hm (k + 1)).1, (AuxKJ_msg W N m hm k).1]
    rcases N with _ | N'
    · simp
    · rw [Finset.sum_range_succ, Finset.sum_range_succ', add_mul, Finset.sum_mul]
      have hs : ∀ i ∈ Finset.range N', (m (k + 1 + i)).poly * X ^ ((N' + 1 - 1 - i) * W) =
          (m (k + (i + 1))).poly * X ^ ((N' + 1 - 1 - (i + 1)) * W) * X ^ W := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [show k + (i + 1) = k + 1 + i by omega, mul_assoc, ← pow_add]
        congr 2
        rw [show N' + 1 - 1 - i = (N' + 1 - 1 - (i + 1)) + 1 by omega, Nat.add_mul, one_mul]
      rw [Finset.sum_congr rfl hs]
      simp only [Nat.add_sub_cancel, Nat.sub_self, zero_mul, pow_zero, mul_one, add_zero,
        Nat.sub_zero]
      rw [show k + 1 + N' = k + (N' + 1) by omega]
      ring
  have hlen : ∀ j, (Msg j).length = N * W := fun j => (AuxKJ_msg W N m hm j).2
  have e2 : crc P u (Msg (k + 1)) v = ((v - u) * X ^ (N * W) + u +
        ∑ n ∈ Finset.range N, (m (k + 1 + n)).poly * X ^ (P.natDegree + W * (N - 1 - n))) % P := by
    unfold crc
    rw [hlen]
    refine congrArg (· % P) ?_
    simp only [Msg]
    rw [(AuxKJ_msg W N m hm (k + 1)).1, Finset.sum_mul]
    have hs : ∀ n ∈ Finset.range N, (m (k + 1 + n)).poly * X ^ ((N - 1 - n) * W) * X ^ P.natDegree =
        (m (k + 1 + n)).poly * X ^ (P.natDegree + W * (N - 1 - n)) := by
      intro n _
      rw [mul_assoc, ← pow_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl hs]
    ring
  have e3 : crc P u (Msg (k + 1)) v = F + G := by
    simp only [F, G]
    rw [← Polynomial.add_mod]
    unfold crc
    rw [add_assoc (_ % P * X ^ W), AuxKJ_mm, hlen, hlen, e1]
    refine congrArg (· % P) ?_
    rw [pow_add]
    ring
  exact ⟨e1, e2, e3, hdeg _, hdeg _⟩

end KadatchJenkins

theorem solution (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (W N : ℕ) (m : ℕ → KadatchJenkins.Message) (hm : ∀ k, (m k).length = W) (v : (ZMod 2)[X]) (k : ℕ) :
    let Msg : ℕ → KadatchJenkins.Message := fun j => (List.range N).flatMap fun n => m (j + n)
    let F := (KadatchJenkins.crc P u (Msg k) v * X ^ W + (m (k + N)).poly * X ^ P.natDegree) % P
    let G := (((v - u) * X ^ (N * W) + u) * (1 - X ^ W) -
      (m k).poly * X ^ (P.natDegree + N * W)) % P
    (Msg (k + 1)).poly = (Msg k).poly * X ^ W - (m k).poly * X ^ (N * W) + (m (k + N)).poly ∧
    KadatchJenkins.crc P u (Msg (k + 1)) v = ((v - u) * X ^ (N * W) + u +
        ∑ n ∈ Finset.range N, (m (k + 1 + n)).poly * X ^ (P.natDegree + W * (N - 1 - n))) % P ∧
      KadatchJenkins.crc P u (Msg (k + 1)) v = F + G ∧ F.degree < (P.natDegree : WithBot ℕ) ∧ G.degree < (P.natDegree : WithBot ℕ) :=
  KadatchJenkins.crc_roll P u hP hu W N m hm v k
