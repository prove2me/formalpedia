-- Prove2me | solution 1 for Martingale.integral_sq_sum_eq_sum_integral_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T00:07:10.205083+00:00
-- url     : https://prove2.me/submissions/2ad69f30-d9f3-4a68-a9e0-2bc11a7eb952

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped ENNReal NNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Increments of a square-integrable martingale difference sequence are orthogonal in `L²`. -/
theorem MDSAux.integral_mul_mds_eq_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m0) (V : ℕ → Ω → ℝ)
    (hmem : ∀ j, MemLp (V j) 2 μ)
    (hadapt : ∀ j, StronglyMeasurable[ℱ (j + 1)] (V j))
    (hmds : ∀ j, μ[V j | ℱ j] =ᵐ[μ] 0) {i j : ℕ} (hij : i < j) :
    ∫ ω, V i ω * V j ω ∂μ = 0 := by
  have hint : ∀ k, Integrable (V k) μ := fun k => (hmem k).integrable one_le_two
  have hintmul : Integrable (fun ω => V i ω * V j ω) μ := (hmem i).integrable_mul (hmem j)
  have hVi : StronglyMeasurable[ℱ j] (V i) := (hadapt i).mono (ℱ.mono (by omega))
  have hpull : μ[fun ω => V i ω * V j ω | ℱ j] =ᵐ[μ] fun ω => V i ω * (μ[V j | ℱ j]) ω := by
    have := condExp_mul_of_stronglyMeasurable_left (m := ℱ j) (μ := μ)
      (f := V i) (g := V j) hVi hintmul (hint j)
    exact this
  have hzero : μ[fun ω => V i ω * V j ω | ℱ j] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hmds j] with ω h1 h2
    simp [h1, h2]
  calc ∫ ω, V i ω * V j ω ∂μ
      = ∫ ω, (μ[fun ω => V i ω * V j ω | ℱ j]) ω ∂μ := (integral_condExp (ℱ.le j)).symm
    _ = 0 := by rw [integral_congr_ae hzero]; simp

/-- **Pythagoras for martingale differences.** -/
theorem MDSAux.integral_sq_sum_eq_sum_integral_sq (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m0) (V : ℕ → Ω → ℝ)
    (hmem : ∀ j, MemLp (V j) 2 μ)
    (hadapt : ∀ j, StronglyMeasurable[ℱ (j + 1)] (V j))
    (hmds : ∀ j, μ[V j | ℱ j] =ᵐ[μ] 0) (n : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range n, V j ω) ^ 2 ∂μ
      = ∑ j ∈ Finset.range n, ∫ ω, (V j ω) ^ 2 ∂μ := by
  have hintmul : ∀ i j, Integrable (fun ω => V i ω * V j ω) μ := fun i j =>
    (hmem i).integrable_mul (hmem j)
  have hexp : (fun ω => (∑ j ∈ Finset.range n, V j ω) ^ 2)
      = fun ω => ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range n, V i ω * V j ω) := by
    funext ω; rw [sq, Finset.sum_mul_sum]
  have hinner : ∀ i, Integrable (fun ω => ∑ j ∈ Finset.range n, V i ω * V j ω) μ := fun i =>
    integrable_finsetSum (μ := μ) (f := fun j ω => V i ω * V j ω) (Finset.range n)
      (fun j _ => hintmul i j)
  rw [hexp, integral_finsetSum (μ := μ)
    (f := fun i ω => ∑ j ∈ Finset.range n, V i ω * V j ω) (Finset.range n) (fun i _ => hinner i)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum (μ := μ) (f := fun j ω => V i ω * V j ω) (Finset.range n)
    (fun j _ => hintmul i j)]
  refine (Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd hi h)).trans ?_
  · rcases lt_or_gt_of_ne hji with h | h
    · have := MDSAux.integral_mul_mds_eq_zero μ ℱ V hmem hadapt hmds h
      simpa [mul_comm] using this
    · exact MDSAux.integral_mul_mds_eq_zero μ ℱ V hmem hadapt hmds h
  · exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (sq (V i ω)).symm)


theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m0) (V : ℕ → Ω → ℝ)
    (hmem : ∀ j, MemLp (V j) 2 μ)
    (hadapt : ∀ j, StronglyMeasurable[ℱ (j + 1)] (V j))
    (hmds : ∀ j, μ[V j | ℱ j] =ᵐ[μ] 0) (n : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range n, V j ω) ^ 2 ∂μ
      = ∑ j ∈ Finset.range n, ∫ ω, (V j ω) ^ 2 ∂μ :=
  MDSAux.integral_sq_sum_eq_sum_integral_sq μ ℱ V hmem hadapt hmds n
