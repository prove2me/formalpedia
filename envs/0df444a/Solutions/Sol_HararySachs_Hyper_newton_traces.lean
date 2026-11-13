-- Prove2me | solution 1 for HararySachs.Hyper.newton_traces
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T20:26:31.131239+00:00
-- url     : https://prove2.me/submissions/2226fc51-d54a-4c49-9e77-a14429b4d75b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Theorems.Thm_HararySachs_Hyper_charPoly_coeff_top
import Theorems.Thm_HararySachs_Hyper_codegCoeff_eq_phiPoly
import Theorems.Thm_HararySachs_Hyper_newtonTr_eq_operator
import Theorems.Thm_HararySachs_Hyper_newtonTr_vTensor

open HararySachs.Hyper Finset

namespace NewtonTracesAux

/-- the defining recursion of `newtonTr`, rearranged into Newton's identity -/
lemma newton_of_newtonTr {R : Type*} [CommRing R] (Φ : Polynomial R) (h0 : Φ.coeff 0 = 1)
    (d : ℕ) (hd : 1 ≤ d) :
    (d : R) * Φ.coeff d = -∑ j ∈ Icc 1 d, newtonTr Φ j * Φ.coeff (d - j) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hrec : newtonTr Φ (e + 1) = -(((e + 1 : ℕ) : R) * Φ.coeff (e + 1)) -
      ∑ j : Fin (e + 1), newtonTr Φ j * Φ.coeff (e + 1 - j) := by
    rw [newtonTr]
  have hIcc : ∑ j ∈ Icc 1 (e + 1), newtonTr Φ j * Φ.coeff (e + 1 - j) =
      ∑ j ∈ range (e + 1), newtonTr Φ j * Φ.coeff (e + 1 - j) + newtonTr Φ (e + 1) := by
    have h1 : range (e + 2) = insert 0 (Icc 1 (e + 1)) := by
      ext j; simp only [mem_range, mem_insert, mem_Icc]; omega
    have h2 := sum_range_succ (fun j => newtonTr Φ j * Φ.coeff (e + 1 - j)) (e + 1)
    rw [h1, sum_insert (by simp), Nat.sub_self, h0, mul_one] at h2
    have hz : newtonTr Φ 0 * Φ.coeff (e + 1 - 0) = 0 := by rw [newtonTr, zero_mul]
    rw [hz, zero_add] at h2
    exact h2
  rw [hIcc, hrec, ← Fin.sum_univ_eq_sum_range (fun j => newtonTr Φ j * Φ.coeff (e + 1 - j))]
  push_cast
  ring

end NewtonTracesAux

open NewtonTracesAux in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (d : ℕ) (hd1 : 1 ≤ d) (hdt : d ≤ n * (k - 1) ^ (n - 1)) :
    (d : ℚ) * codegCoeff (k := k) E res d =
      -∑ j ∈ Finset.Icc 1 d, Tr (k := k) E j * codegCoeff (k := k) E res (d - j) := by
  classical
  set A : Fin n → (Fin (k - 1) → Fin n) → ℚ := fun i t => adjEntry E (Fin.cons i t) with hA
  set Φ : Polynomial ℚ := phiPoly (k := k) A res with hΦ
  -- A1: the codegree coefficients are the coefficients of `Φ(z) = Res(x^{[k-1]} - z A x^{k-1})`
  have hc : ∀ j ≤ d, codegCoeff (k := k) E res j = Φ.coeff j := fun j hj =>
    codegCoeff_eq_phiPoly n k hk hn E res hres j (hj.trans hdt)
  have h0 : Φ.coeff 0 = 1 := by
    rw [← hc 0 (Nat.zero_le _)]
    unfold codegCoeff
    rw [Nat.sub_zero]
    exact charPoly_coeff_top n k hk hn E hE res hres
  -- the Morozov–Shakirov traces are the Newton traces of `Φ`
  have hTr : ∀ j, 1 ≤ j → Tr (k := k) E j = newtonTr Φ j := by
    intro j hj
    rw [hΦ, newtonTr_eq_operator n k hk hn res hres A j hj, Tr, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    split_ifs with ha
    · rw [newtonTr_vTensor n k hk hn res hres A j hj a ha, mul_div_assoc]
      rfl
    · rw [mul_zero]
  rw [hc d le_rfl, newton_of_newtonTr Φ h0 d hd1]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [mem_Icc] at hj
  rw [hTr j hj.1, hc (d - j) (Nat.sub_le d j)]
