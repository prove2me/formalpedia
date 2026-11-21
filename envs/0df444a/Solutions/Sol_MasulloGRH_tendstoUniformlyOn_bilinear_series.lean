-- Prove2me | solution 1 for MasulloGRH.tendstoUniformlyOn_bilinear_series
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:18:19.204722+00:00
-- url     : https://prove2.me/submissions/5fc7e1f3-784c-4e03-b95b-3e2b8f258623

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Filter Topology Set Bornology
open scoped Pointwise

private theorem equicontinuous_bounded_family {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (f : ℕ → StrongDual ℂ E)
    (hf : Equicontinuous (fun i => (f i : E → ℂ))) {S : Set E}
    (hS : IsVonNBounded ℂ S) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ S → ‖f i x‖ ≤ C := by
  let U : Set E := {x | ∀ i, ‖f i x‖ < 1}
  have hU : U ∈ 𝓝 0 := by
    filter_upwards [Metric.equicontinuousAt_iff_right.mp (hf 0) 1 zero_lt_one] with x hx
    intro i
    simpa [dist_comm (0 : ℂ), dist_eq_norm] using hx i
  obtain ⟨a, ha⟩ := (hS hU).eventually.exists
  refine ⟨‖a‖, norm_nonneg _, fun i x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := ha hx
  rw [map_smul, norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg a) (hy i).le

theorem solution (E F : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (φ : ℕ → StrongDual ℂ E) (ψ : ℕ → StrongDual ℂ F) (c : ℕ → ℂ)
    (hφ : Equicontinuous (fun m => (φ m : E → ℂ))) (hψ : Equicontinuous (fun m => (ψ m : F → ℂ)))
    (hc : Summable (fun m => ‖c m‖)) (B : E → F → ℂ)
    (hsum : ∀ x y, HasSum (fun m => c m * φ m x * ψ m y) (B x y))
    (S : Set E) (T : Set F) (hS : Bornology.IsVonNBounded ℂ S)
    (hT : Bornology.IsVonNBounded ℂ T) :
    TendstoUniformlyOn
      (fun (k : ℕ) (p : E × F) => ∑ m ∈ Finset.range k, c m * φ m p.1 * ψ m p.2)
      (fun p : E × F => B p.1 p.2) Filter.atTop (S ×ˢ T) := by
  obtain ⟨C, hC, hCx⟩ := equicontinuous_bounded_family φ hφ hS
  obtain ⟨D, hD, hDy⟩ := equicontinuous_bounded_family ψ hψ hT
  refine (tendstoUniformlyOn_tsum_nat ((hc.mul_right C).mul_right D)
    (f := fun m (p : E × F) => c m * φ m p.1 * ψ m p.2) (s := S ×ˢ T) ?_).congr_right ?_
  · intro m p hp
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hCx m p.1 hp.1) (norm_nonneg _))
      (hDy m p.2 hp.2) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hC)
  · intro p _
    exact (hsum p.1 p.2).tsum_eq
