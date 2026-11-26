-- Prove2me | solution 1 for Malliavin.integral_inner_symmetrizeL_eq_factorial_smul_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:15.414145+00:00
-- url     : https://prove2.me/submissions/e7e40427-e2f3-46c4-9bea-bd6132a7797b

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_coeFn_symmetrizeL
import Theorems.Thm_Malliavin_integral_eq_factorial_smul_setIntegral_simplex
import Theorems.Thm_Malliavin_isSymmetric_symmetrize


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (n : ℕ)
    (f g : IteratedKernel n) :
    (∫ t, inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f t)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g t)
        ∂iteratedKernelMeasure n) =
      n.factorial • ∫ t in simplex ℝ≥0 n, inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f t)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g t)
        ∂iteratedKernelMeasure n := by
  let sf := symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f
  let sg := symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g
  have hf := coeFn_symmetrizeL (E := ℝ) (μ := nonnegativeLebesgueMeasure) n 2 f
  have hg := coeFn_symmetrizeL (E := ℝ) (μ := nonnegativeLebesgueMeasure) n 2 g
  have hinner :
      (fun t => inner ℝ (sf t) (sg t)) =ᵐ[iteratedKernelMeasure n]
        fun t => inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t) := by
    filter_upwards [hf, hg] with t hft hgt
    exact congrArg₂ (inner ℝ) hft hgt
  have hsym : IsSymmetric n
      (fun t => inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t)) := by
    intro σ t
    change inner ℝ (symmetrize n (⇑f) (t ∘ σ)) (symmetrize n (⇑g) (t ∘ σ)) =
      inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t)
    rw [isSymmetric_symmetrize n (⇑f) σ t, isSymmetric_symmetrize n (⇑g) σ t]
  have hint : Integrable
      (fun t => inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t))
      (iteratedKernelMeasure n) :=
    (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) sf sg).congr hinner
  have htile := integral_eq_factorial_smul_setIntegral_simplex
    (μ := nonnegativeLebesgueMeasure) hsym hint
  calc
    (∫ t, inner ℝ (sf t) (sg t) ∂iteratedKernelMeasure n) =
        ∫ t, inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t)
          ∂iteratedKernelMeasure n := integral_congr_ae hinner
    _ = n.factorial • ∫ t in simplex ℝ≥0 n,
          inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t)
          ∂iteratedKernelMeasure n := htile
    _ = n.factorial • ∫ t in simplex ℝ≥0 n, inner ℝ (sf t) (sg t)
          ∂iteratedKernelMeasure n := by
      congr 1
      exact integral_congr_ae hinner.restrict.symm
end Malliavin
