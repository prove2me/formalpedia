-- Prove2me | solution 1 for MeasureTheory.memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d5b40f7d-03a7-544f-80d5-ee8d67a1db58

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

namespace L2ErrAux

theorem aux_norm_add_sq_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  nlinarith [mul_nonneg (norm_nonneg (a + b)) (sub_nonneg.2 (norm_add_le a b)),
    mul_self_nonneg (‖a‖ + ‖b‖ - ‖a + b‖), sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem aux_integrable_norm_sq {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun x => ‖f x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf

end L2ErrAux

open L2ErrAux in
theorem solution
    {n m : ℕ} (κ τ₁ τ₂ : ℝ)
    (T F d : Fin n → ℝ → ℂ) (d' : Fin m → ℝ → ℂ) (B : Fin n → Fin m → ℝ → ℂ)
    (_hd : ∀ j, MemLp (d j) 2) (_hd' : ∀ j', MemLp (d' j') 2)
    (_hTF : ∀ j, AEStronglyMeasurable (fun t => T j t - F j t))
    (_hB : ∀ (t : ℝ) (x : Fin m → ℂ),
      ∑ j : Fin n, ‖∑ j' : Fin m, conj (B j j' t) * x j'‖ ^ 2 ≤ ∑ j' : Fin m, ‖x j'‖ ^ 2)
    (_heq : ∀ (j : Fin n) (t : ℝ),
      T j (t + τ₁) - F j (t + τ₁) = (κ : ℂ) * (d j (t + τ₁) + ∑ j' : Fin m, conj (B j j' t) * d' j' (-t + τ₂))) :
    (∀ j : Fin n, MemLp (fun t => F j t - T j t) 2) ∧
    ∫ t : ℝ, ∑ j : Fin n, ‖F j t - T j t‖ ^ 2 ≤
      2 * κ ^ 2 * ((∑ j : Fin n, ∫ t : ℝ, ‖d j t‖ ^ 2) + ∑ j' : Fin m, ∫ t : ℝ, ‖d' j' t‖ ^ 2) := by

  have key : ∀ (j : Fin n) (s : ℝ), F j s - T j s
      = -((κ : ℂ) * (d j s + ∑ j' : Fin m, conj (B j j' (s - τ₁)) * d' j' (-(s - τ₁) + τ₂))) := by
    intro j s
    have h := _heq j (s - τ₁)
    simp only [sub_add_cancel] at h
    rw [← h]
    ring

  have hpt : ∀ s : ℝ, ∑ j : Fin n, ‖F j s - T j s‖ ^ 2
      ≤ 2 * κ ^ 2 * (∑ j : Fin n, ‖d j s‖ ^ 2 + ∑ j' : Fin m, ‖d' j' (-(s - τ₁) + τ₂)‖ ^ 2) := by
    intro s
    have hB := _hB (s - τ₁) (fun j' => d' j' (-(s - τ₁) + τ₂))
    calc ∑ j : Fin n, ‖F j s - T j s‖ ^ 2
        = κ ^ 2 * ∑ j : Fin n, ‖d j s + ∑ j' : Fin m, conj (B j j' (s - τ₁)) * d' j' (-(s - τ₁) + τ₂)‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [key, norm_neg, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ κ ^ 2 * ∑ j : Fin n, 2 * (‖d j s‖ ^ 2
            + ‖∑ j' : Fin m, conj (B j j' (s - τ₁)) * d' j' (-(s - τ₁) + τ₂)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => aux_norm_add_sq_le _ _) (sq_nonneg _)
      _ = 2 * κ ^ 2 * (∑ j : Fin n, ‖d j s‖ ^ 2
            + ∑ j : Fin n, ‖∑ j' : Fin m, conj (B j j' (s - τ₁)) * d' j' (-(s - τ₁) + τ₂)‖ ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          ring
      _ ≤ 2 * κ ^ 2 * (∑ j : Fin n, ‖d j s‖ ^ 2 + ∑ j' : Fin m, ‖d' j' (-(s - τ₁) + τ₂)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [hB]) (by positivity)

  have hId : ∀ j : Fin n, Integrable (fun s : ℝ => ‖d j s‖ ^ 2) := fun j => aux_integrable_norm_sq (_hd j)
  have hrefl : ∀ j' : Fin m, (fun s : ℝ => ‖d' j' (-(s - τ₁) + τ₂)‖ ^ 2)
      = fun s : ℝ => (fun u : ℝ => ‖d' j' u‖ ^ 2) (τ₁ + τ₂ - s) := by
    intro j'
    funext s
    rw [show -(s - τ₁) + τ₂ = τ₁ + τ₂ - s by ring]
  have hId' : ∀ j' : Fin m, Integrable (fun s : ℝ => ‖d' j' (-(s - τ₁) + τ₂)‖ ^ 2) := fun j' => by
    rw [hrefl j']
    exact (aux_integrable_norm_sq (_hd' j')).comp_sub_left (τ₁ + τ₂)
  have hA : Integrable (fun s : ℝ => ∑ j : Fin n, ‖d j s‖ ^ 2) :=
    integrable_finsetSum Finset.univ fun j _ => hId j
  have hA' : Integrable (fun s : ℝ => ∑ j' : Fin m, ‖d' j' (-(s - τ₁) + τ₂)‖ ^ 2) :=
    integrable_finsetSum Finset.univ fun j' _ => hId' j'
  have hIM : Integrable (fun s : ℝ => 2 * κ ^ 2
      * (∑ j : Fin n, ‖d j s‖ ^ 2 + ∑ j' : Fin m, ‖d' j' (-(s - τ₁) + τ₂)‖ ^ 2)) :=
    (hA.add hA').const_mul (2 * κ ^ 2)

  have hmeas : ∀ j : Fin n, AEStronglyMeasurable (fun t : ℝ => F j t - T j t) := fun j => by
    have e : (fun t : ℝ => -(T j t - F j t)) = (fun t : ℝ => F j t - T j t) := funext fun t => neg_sub _ _
    rw [← e]
    exact (_hTF j).neg
  refine ⟨fun j => ?_, ?_⟩
  · refine (memLp_two_iff_integrable_sq_norm (hmeas j)).2 ?_
    refine hIM.mono' ((continuous_pow 2).comp_aestronglyMeasurable (hmeas j).norm)
      (Filter.Eventually.of_forall fun s => ?_)
    rw [norm_pow, norm_norm]
    exact (Finset.single_le_sum (f := fun i : Fin n => ‖F i s - T i s‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)).trans (hpt s)
  · have hint : ∀ j' : Fin m, (∫ s : ℝ, ‖d' j' (-(s - τ₁) + τ₂)‖ ^ 2) = ∫ t : ℝ, ‖d' j' t‖ ^ 2 :=
      fun j' => by
        rw [hrefl j']
        exact integral_sub_left_eq_self (fun u : ℝ => ‖d' j' u‖ ^ 2) volume (τ₁ + τ₂)
    calc ∫ t : ℝ, ∑ j : Fin n, ‖F j t - T j t‖ ^ 2
        ≤ ∫ s : ℝ, 2 * κ ^ 2
            * (∑ j : Fin n, ‖d j s‖ ^ 2 + ∑ j' : Fin m, ‖d' j' (-(s - τ₁) + τ₂)‖ ^ 2) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun s =>
            Finset.sum_nonneg fun j _ => sq_nonneg _) hIM (Filter.Eventually.of_forall hpt)
      _ = 2 * κ ^ 2 * ((∑ j : Fin n, ∫ t : ℝ, ‖d j t‖ ^ 2) + ∑ j' : Fin m, ∫ t : ℝ, ‖d' j' t‖ ^ 2) := by
          rw [integral_const_mul, integral_add hA hA', integral_finsetSum _ (fun j _ => hId j),
            integral_finsetSum _ (fun j' _ => hId' j')]
          simp only [hint]

end S_MeasureTheory_memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel
end P2MW
export P2MW.S_MeasureTheory_memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel (solution)
