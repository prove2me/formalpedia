-- Prove2me | solution 1 for MeasureTheory.exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b78b7b5b-57a7-5fe3-a902-8583aa66a564

import Mathlib
import Theorems.Thm_Real_norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff
import Theorems.Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic
import Theorems.Thm_Summable_exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic

set_option autoImplicit false

open MeasureTheory

theorem solution
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p) :
    (∀ m : Fin c → ℤ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin r → ℝ =>
        ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) ∧
      ∀ x : Fin r → ℝ, (∃ k, R < |x k|) →
        (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) = 0) ∧
    ∃ C : (Fin c → ℤ) → ℝ, Summable C ∧ (∀ m, 0 ≤ C m) ∧
      (∀ (m : Fin c → ℤ) (x : Fin r → ℝ),
        ‖(∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))‖ ≤ C m * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
      (∀ (m : Fin c → ℤ) (ξ : Fin r → ℝ),
        ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) *
            (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))‖ ≤
          C m * ∏ k, (1 + |ξ k|)⁻¹ ^ 2) := by
  obtain ⟨M, hM0, hM⟩ :=
    MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic
      W hW R hR hsupp hper
  refine ⟨fun m => ⟨(hM m).1, (hM m).2.1⟩, ?_⟩
  refine ⟨fun m => M * (∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2) * ((1 + R) ^ (2 * r) + (8 * R) ^ r), ?_, ?_, ?_, ?_⟩
  · have hS : Summable fun m : Fin c → ℤ => ∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2 := by
      obtain ⟨K, hK⟩ :=
        Summable.exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective c c
          LinearMap.id (fun _ _ h => h)
      simpa using (hK 0).1
    exact (hS.mul_left M).mul_right _
  · intro m
    exact mul_nonneg (mul_nonneg hM0 (Finset.prod_nonneg fun j _ => by positivity)) (by positivity)
  · intro m x
    exact (Real.norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff
      (fun x : Fin r → ℝ =>
        ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))
      R (M * ∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2) hR ((hM m).1.of_le (by exact_mod_cast le_top)) (hM m).2.1 (hM m).2.2).1 x
  · intro m ξ
    exact (Real.norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff
      (fun x : Fin r → ℝ =>
        ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))
      R (M * ∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2) hR ((hM m).1.of_le (by exact_mod_cast le_top)) (hM m).2.1 (hM m).2.2).2 ξ

end S_MeasureTheory_exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic
end P2MW
export P2MW.S_MeasureTheory_exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic (solution)
