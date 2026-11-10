-- Prove2me | solution 1 for MinFracProphet.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:21:41.465395+00:00
-- url     : https://prove2.me/submissions/b79464e7-02a0-4658-9131-ca375a4ab7ab

import Mathlib
import Definitions.Def_MinFracProphet_Model

namespace Aux_MinFrac_l1

theorem tangent (x y p : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (hp : 1 ≤ p) :
    y ^ p + p * y ^ (p - 1) * (x - y) ≤ x ^ p := by
  have h := one_add_mul_self_le_rpow_one_add (s := x / y - 1)
    (by have := div_nonneg hx hy.le; linarith) hp
  rw [add_sub_cancel, Real.div_rpow hx hy.le] at h
  have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy p
  rw [le_div_iff₀ hyp] at h
  rw [Real.rpow_sub_one hy.ne' p]
  calc y ^ p + p * (y ^ p / y) * (x - y) = (1 + p * (x / y - 1)) * y ^ p := by
        field_simp
    _ ≤ x ^ p := h

end Aux_MinFrac_l1

open MinFracProphet in
theorem solution (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 1 < p) (q : ℝ) (hq : q = -1 / (p - 1))
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    IsLeast (procCost p c '' simplex n) ((∑ i, c i ^ q) ^ (1 / q)) ∧
      OPT p c = (∑ i, c i ^ q) ^ (1 / q) := by
  have hp1 : p - 1 ≠ 0 := by linarith
  have hcq : ∀ i, 0 < c i ^ q := fun i => Real.rpow_pos_of_pos (hc i) q
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑ i, c i ^ q := ⟨_, rfl⟩
  rw [← hSdef]
  have hS : 0 < S := by
    rw [hSdef]
    exact Finset.sum_pos (fun i _ => hcq i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun i => c i ^ q / S := ⟨_, rfl⟩
  have hypos : ∀ i, 0 < y i := fun i => by rw [hy]; exact div_pos (hcq i) hS
  have hysum : ∑ i, y i = 1 := by
    rw [hy]
    simp only
    rw [← Finset.sum_div, ← hSdef, div_self hS.ne']
  have hymem : y ∈ simplex n := by
    refine ⟨fun i => ⟨(hypos i).le, ?_⟩, hysum⟩
    rw [← hysum]
    exact Finset.single_le_sum (fun j _ => (hypos j).le) (Finset.mem_univ i)
  have hqp : 1 + q * p = q := by rw [hq]; first | (field_simp; ring1) | field_simp
  have hqp1 : q * (p - 1) = -1 := by rw [hq]; first | (field_simp; ring1) | field_simp
  have hinvq : 1 / q = 1 - p := by rw [hq]; first | (field_simp; ring1) | field_simp
  have hci : ∀ i, c i ^ q = c i * c i ^ (q * p) := by
    intro i
    conv_lhs => rw [← hqp]
    rw [Real.rpow_add (hc i), Real.rpow_one]
  have hcy : ∀ i, c i * y i ^ p = c i ^ q / S ^ p := by
    intro i
    rw [hy]
    simp only
    rw [Real.div_rpow (hcq i).le hS.le, ← Real.rpow_mul (hc i).le, mul_div_assoc', ← hci]
  have hcy1 : ∀ i, c i * y i ^ (p - 1) = 1 / S ^ (p - 1) := by
    intro i
    rw [hy]
    simp only
    rw [Real.div_rpow (hcq i).le hS.le, ← Real.rpow_mul (hc i).le, hqp1, Real.rpow_neg_one,
      mul_div_assoc', mul_inv_cancel₀ (hc i).ne']
  have hV : procCost p c y = S ^ (1 / q) := by
    unfold procCost
    rw [Finset.sum_congr rfl (fun i _ => hcy i), ← Finset.sum_div, ← hSdef, hinvq,
      Real.rpow_sub hS, Real.rpow_one]
  have hleast : IsLeast (procCost p c '' simplex n) (S ^ (1 / q)) := by
    refine ⟨⟨y, hymem, hV⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hterm : ∀ i, c i * y i ^ p + p * (1 / S ^ (p - 1)) * (x i - y i) ≤ c i * x i ^ p := by
      intro i
      have h1 := Aux_MinFrac_l1.tangent (x i) (y i) p (hx.1 i).1 (hypos i) hp.le
      have h2 := mul_le_mul_of_nonneg_left h1 (hc i).le
      calc c i * y i ^ p + p * (1 / S ^ (p - 1)) * (x i - y i)
          = c i * (y i ^ p + p * y i ^ (p - 1) * (x i - y i)) := by
            linear_combination (-(p * (x i - y i))) * hcy1 i
        _ ≤ c i * x i ^ p := h2
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hx.2, hysum, sub_self,
      mul_zero, add_zero] at hsum
    rw [← hV]
    exact hsum
  exact ⟨hleast, hleast.csInf_eq⟩
