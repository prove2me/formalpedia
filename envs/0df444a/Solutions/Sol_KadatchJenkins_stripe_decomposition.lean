-- Prove2me | solution 1 for KadatchJenkins.stripe_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:14:51.708814+00:00
-- url     : https://prove2.me/submissions/9f80467f-6c36-4029-a5ff-eed4af3ebcc8

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

theorem stripe_decomposition (W N K : ℕ) (hN : 0 < N) (m : ℕ → ℕ → Message) (hm : ∀ k n, (m k n).length = W) :
    let M : Message := (List.range K).flatMap fun k => (List.range N).flatMap fun n => m k n
    let Mn : ℕ → (ZMod 2)[X] := fun n =>
      ∑ k ∈ Finset.range K, (m k n).poly * X ^ ((K - 1 - k) * (N * W))
    let M' : ℕ → Message := fun n =>
      (List.range K).flatMap fun k => m k n ++ List.replicate ((N - 1) * W) 0
    M.poly = ∑ n ∈ Finset.range N, Mn n * X ^ ((N - 1 - n) * W) ∧
      (∀ n, (M' n).poly = Mn n * X ^ ((N - 1) * W) ∧ (M' n).length = K * (N * W)) ∧
      M.poly * X ^ ((N - 1) * W) = ∑ n ∈ Finset.range N, (M' n).poly * X ^ ((N - 1 - n) * W) := by
  intro M Mn M'
  have hblk : ∀ k, ((List.range N).flatMap fun n => m k n).length = N * W :=
    fun k => (AuxKJ_G W (m k) (hm k) N).2
  have e1 : M.poly = ∑ n ∈ Finset.range N, Mn n * X ^ ((N - 1 - n) * W) := by
    rw [(AuxKJ_G (N * W) _ hblk K).1]
    simp only [Mn]
    simp_rw [(AuxKJ_G W (m _) (hm _) N).1, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  have hlen : ∀ n k, (m k n ++ List.replicate ((N - 1) * W) 0).length = N * W := by
    intro n k
    rw [List.length_append, List.length_replicate, hm]
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    simp [Nat.add_mul, add_comm]
  have e2 : ∀ n, (M' n).poly = Mn n * X ^ ((N - 1) * W) ∧ (M' n).length = K * (N * W) := by
    intro n
    obtain ⟨g1, g2⟩ := AuxKJ_G (N * W) (fun k => m k n ++ List.replicate ((N - 1) * W) 0) (hlen n) K
    refine ⟨?_, g2⟩
    simp only [M', Mn]
    rw [g1, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [AuxKJ_poly_append, AuxKJ_rep, List.length_replicate]
    ring
  refine ⟨e1, e2, ?_⟩
  rw [e1, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [(e2 n).1]
  ring

end KadatchJenkins

theorem solution (W N K : ℕ) (hN : 0 < N) (m : ℕ → ℕ → KadatchJenkins.Message) (hm : ∀ k n, (m k n).length = W) :
    let M : KadatchJenkins.Message := (List.range K).flatMap fun k => (List.range N).flatMap fun n => m k n
    let Mn : ℕ → (ZMod 2)[X] := fun n =>
      ∑ k ∈ Finset.range K, (m k n).poly * X ^ ((K - 1 - k) * (N * W))
    let M' : ℕ → KadatchJenkins.Message := fun n =>
      (List.range K).flatMap fun k => m k n ++ List.replicate ((N - 1) * W) 0
    M.poly = ∑ n ∈ Finset.range N, Mn n * X ^ ((N - 1 - n) * W) ∧
      (∀ n, (M' n).poly = Mn n * X ^ ((N - 1) * W) ∧ (M' n).length = K * (N * W)) ∧
      M.poly * X ^ ((N - 1) * W) = ∑ n ∈ Finset.range N, (M' n).poly * X ^ ((N - 1 - n) * W) :=
  KadatchJenkins.stripe_decomposition W N K hN m hm
