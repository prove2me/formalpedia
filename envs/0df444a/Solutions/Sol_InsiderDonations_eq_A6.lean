-- Prove2me | solution 1 for InsiderDonations.eq_A6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:12:42.497605+00:00
-- url     : https://prove2.me/submissions/d1742cb3-7494-44d9-a9d3-e54f66a4726d

import Mathlib
import Definitions.Def_InsiderDonations_Model

open MeasureTheory ProbabilityTheory

namespace Aux_InsiderDonations_eq_A6

theorem L1 (p q r s x : ℝ) (hden : r + s * x ≠ 0) :
    HasDerivAt (fun y => (p + q * y) / (r + s * y))
      ((q * (r + s * x) - (p + q * x) * s) / (r + s * x) ^ 2) x := by
  have hN : HasDerivAt (fun y => p + q * y) q x := by
    simpa using ((hasDerivAt_id x).const_mul q).const_add p
  have hD : HasDerivAt (fun y => r + s * y) s x := by
    simpa using ((hasDerivAt_id x).const_mul s).const_add r
  exact hN.div hD hden

end Aux_InsiderDonations_eq_A6

open InsiderDonations Aux_InsiderDonations_eq_A6 in
theorem solution (m n τo τc σv : ℝ) (hσv : 0 < σv) (hA : (1 + m) * τo - m * (1 - τc) ≠ 0) :
    HasDerivAt (fun x => OmegaF x n τo τc σv)
      (τo * ((1 + n) * (1 - τc) - n * τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) m ∧
    HasDerivAt (fun x => OmegaF m x τo τc σv)
      (τo / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)))) n ∧
    HasDerivAt (fun t => OmegaF m n t τc σv)
      (-(m * (1 + m + n) * (1 - τc)) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) τo ∧
    HasDerivAt (fun t => OmegaF m n τo t σv)
      (-(m * (1 + m + n) * τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) τc ∧
    deriv (fun x => OmegaF x n τo τc σv) m - deriv (fun x => OmegaF m x τo τc σv) n =
      (1 + m + n) * τo * (1 - τc - τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2) ∧
    (0 < m → 0 ≤ n → 0 < τo → τc ≤ τo → τo < 1 / 2 → 0 < (1 + m) * τo - m * (1 - τc) →
      0 < τo * ((1 + n) * (1 - τc) - n * τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2) ∧
      0 < τo / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc))) ∧
      -(m * (1 + m + n) * (1 - τc)) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2) < 0 ∧
      -(m * (1 + m + n) * τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2) < 0 ∧
      0 < (1 + m + n) * τo * (1 - τc - τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) := by
  have hσ0 : σv ≠ 0 := hσv.ne'
  have hσ2 : σv ^ 2 ≠ 0 := pow_ne_zero 2 hσ0
  have hden0 : σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ≠ 0 := mul_ne_zero hσ2 hA
  have d1 : HasDerivAt (fun x => OmegaF x n τo τc σv)
      (τo * ((1 + n) * (1 - τc) - n * τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) m := by
    have e : (fun x => OmegaF x n τo τc σv) = fun y =>
        ((1 + n) * τo + τo * y) / (σv ^ 2 * τo + σv ^ 2 * (τo - (1 - τc)) * y) := by
      funext y
      unfold OmegaF
      congr 1 <;> ring
    have hden : σv ^ 2 * τo + σv ^ 2 * (τo - (1 - τc)) * m ≠ 0 := by
      have h' : σv ^ 2 * τo + σv ^ 2 * (τo - (1 - τc)) * m =
          σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) := by ring
      rw [h']; exact hden0
    rw [e]
    refine (L1 _ _ _ _ m hden).congr_deriv ?_
    field_simp <;> ring
  have d2 : HasDerivAt (fun x => OmegaF m x τo τc σv)
      (τo / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)))) n := by
    have e : (fun x => OmegaF m x τo τc σv) = fun y =>
        ((1 + m) * τo + τo * y) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) + 0 * y) := by
      funext y
      unfold OmegaF
      congr 1 <;> ring
    have hden : σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) + 0 * n ≠ 0 := by
      rw [zero_mul, add_zero]; exact hden0
    rw [e]
    refine (L1 _ _ _ _ n hden).congr_deriv ?_
    rw [div_eq_div_iff (pow_ne_zero 2 hden) hden0]
    ring
  have d3 : HasDerivAt (fun t => OmegaF m n t τc σv)
      (-(m * (1 + m + n) * (1 - τc)) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) τo := by
    have e : (fun t => OmegaF m n t τc σv) = fun y =>
        (0 + (1 + m + n) * y) / (σv ^ 2 * (-(m * (1 - τc))) + σv ^ 2 * (1 + m) * y) := by
      funext y
      unfold OmegaF
      congr 1 <;> ring
    have hden : σv ^ 2 * (-(m * (1 - τc))) + σv ^ 2 * (1 + m) * τo ≠ 0 := by
      have h' : σv ^ 2 * (-(m * (1 - τc))) + σv ^ 2 * (1 + m) * τo =
          σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) := by ring
      rw [h']; exact hden0
    rw [e]
    refine (L1 _ _ _ _ τo hden).congr_deriv ?_
    rw [div_eq_div_iff (pow_ne_zero 2 hden) (mul_ne_zero hσ2 (pow_ne_zero 2 hA))]
    ring
  have d4 : HasDerivAt (fun t => OmegaF m n τo t σv)
      (-(m * (1 + m + n) * τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) τc := by
    have e : (fun t => OmegaF m n τo t σv) = fun y =>
        ((1 + m + n) * τo + 0 * y) / (σv ^ 2 * ((1 + m) * τo - m) + σv ^ 2 * m * y) := by
      funext y
      unfold OmegaF
      congr 1 <;> ring
    have hden : σv ^ 2 * ((1 + m) * τo - m) + σv ^ 2 * m * τc ≠ 0 := by
      have h' : σv ^ 2 * ((1 + m) * τo - m) + σv ^ 2 * m * τc =
          σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) := by ring
      rw [h']; exact hden0
    rw [e]
    refine (L1 _ _ _ _ τc hden).congr_deriv ?_
    rw [div_eq_div_iff (pow_ne_zero 2 hden) (mul_ne_zero hσ2 (pow_ne_zero 2 hA))]
    ring
  refine ⟨d1, d2, d3, d4, ?_, ?_⟩
  · rw [d1.deriv, d2.deriv]
    field_simp <;> ring
  · intro hm hn hτo hτ hτ2 hA'
    have hden2 : 0 < σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2 :=
      mul_pos (pow_pos hσv 2) (pow_pos hA' 2)
    have hden1 : 0 < σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) := mul_pos (pow_pos hσv 2) hA'
    have hN : 0 < 1 + m + n := by linarith
    have h1c : 0 < 1 - τc := by linarith
    have hgap : 0 < 1 - τc - τo := by linarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply div_pos _ hden2
      apply mul_pos hτo
      nlinarith
    · exact div_pos hτo hden1
    · apply div_neg_of_neg_of_pos _ hden2
      have := mul_pos (mul_pos hm hN) h1c
      linarith
    · apply div_neg_of_neg_of_pos _ hden2
      have := mul_pos (mul_pos hm hN) hτo
      linarith
    · exact div_pos (mul_pos (mul_pos hN hτo) hgap) hden2
