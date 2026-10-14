-- Prove2me | solution 1 for IntMul.HvdH.dftC_eq_dftBox
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T02:56:42.44176+00:00
-- url     : https://prove2.me/submissions/85662be7-c188-40bd-b9f2-5e4e46aba557

import Definitions.Def_IntMul_HvdH_ExactConv

open Finset Complex

namespace IntMul.HvdH.DAd
open IntMul.HvdH

lemma om_zpow_neg (N a : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I / N) ^ (-((a : ℕ) : ℤ)) =
      Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ) / N)) := by
  rw [← Complex.exp_int_mul]; congr 1; push_cast; ring

lemma sum_snoc {d : ℕ} (t : Fin d → ℕ) (r : ℕ) (f : (Fin (d + 1) → ℕ) → ℂ) :
    ∑ K ∈ Fintype.piFinset (fun i => range ((Fin.snoc t r : Fin (d + 1) → ℕ) i)), f K =
      ∑ k ∈ Fintype.piFinset (fun i => range (t i)), ∑ c ∈ range r, f (Fin.snoc k c) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun K => (Fin.init K, K (Fin.last d))) (fun kc => Fin.snoc kc.1 kc.2)
    ?_ ?_ ?_ ?_ ?_
  · intro K hK
    have h := Fintype.mem_piFinset.1 hK
    simp only [mem_product, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · have := h i.castSucc; simpa [Fin.init] using this
    · have := h (Fin.last d); simpa using this
  · intro kc hkc
    simp only [mem_product, Fintype.mem_piFinset] at hkc
    simp only [Fintype.mem_piFinset]
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hkc.2
    · simpa using hkc.1 i
  · intro K _; simp
  · intro kc _; simp
  · intro K _; simp

theorem dftC_eq_dftBox {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (x : (Fin (d + 1) → ℕ) → ℂ)
    (j : Fin (d + 1) → ℕ) (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    dftC r e x j = dftBox (Fin.snoc (fun i => 2 ^ e i) r) x j := by
  have hj' : ∀ i, j i < (Fin.snoc (fun i => 2 ^ e i) r : Fin (d + 1) → ℕ) i := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hc
    · simpa using hj i
  unfold dftBox dftC
  rw [if_pos hj', sum_snoc]
  congr 1
  · rw [Fin.prod_univ_castSucc]; simp [Finset.prod_pow_eq_pow_sum, mul_comm]
  · apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro c _
    congr 1
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, om_zpow_neg]
    rw [← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    push_cast
    rw [mul_add, Finset.mul_sum, neg_add, ← Finset.sum_neg_distrib]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; ring
    · ring

end IntMul.HvdH.DAd

open IntMul.HvdH

theorem solution {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (x : (Fin (d + 1) → ℕ) → ℂ)
    (j : Fin (d + 1) → ℕ) (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    dftC r e x j = dftBox (Fin.snoc (fun i => 2 ^ e i) r) x j :=
  IntMul.HvdH.DAd.dftC_eq_dftBox r e x j hj hc
