-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_jump_step_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:30:20.309554+00:00
-- url     : https://prove2.me/submissions/422fd0e0-e0d9-4182-a8ac-aae14c6e522e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_finite_step_integral_identity
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_jump_threshold_integral
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Apply finite-step integral linearity to the jump energy and identify each strict threshold with the cumulative energy difference. -/
theorem solution
    (μ : Measure (ℝ × ℝ)) (t : NNReal)
    (hi : IntegrableOn (fun z : ℝ × ℝ => z.2^2/2)
      (Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ)) μ)
    (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ) :
    let W : ℝ → ℝ := fun s =>
      ∑ i ∈ Finset.range m, c i * (if (b i:ℝ) < s then (1:ℝ) else 0)
    let S : Set (ℝ × ℝ) := Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ)
    IntegrableOn (fun z : ℝ × ℝ => W z.1 * (z.2^2/2)) S μ ∧
      (∫ z in S, W z.1 * (z.2^2/2) ∂μ) =
        ∑ i ∈ Finset.range m, c i *
          ((∫ z in S, z.2^2/2 ∂μ) -
           ∫ z in Icc (0:ℝ) ((min t (b i):NNReal):ℝ) ×ˢ (univ : Set ℝ),
             z.2^2/2 ∂μ) := by
  intro W S
  let D : ℕ → Set (ℝ × ℝ) := fun i => {z | (b i:ℝ) < z.1}
  let e : ℝ × ℝ → ℝ := fun z => z.2^2/2
  obtain ⟨hWi,hWe⟩ := Kyprianou.Ch04.ito43_finite_step_integral_identity
    μ S e hi m D (fun i => measurableSet_lt measurable_const measurable_fst) c
  dsimp only at hWi hWe
  have hfun : (fun z : ℝ × ℝ => (∑ i ∈ Finset.range m,
      c i * (D i).indicator (fun _ => (1:ℝ)) z) * e z) =
      (fun z => W z.1 * e z) := by
    funext z
    simp [W,D,Set.indicator]
  rw [hfun] at hWi hWe
  refine ⟨hWi,hWe.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i hi'
  exact congrArg (fun x => c i*x)
    (Kyprianou.Ch04.ito43_qv_jump_threshold_integral μ t (b i) hi)
