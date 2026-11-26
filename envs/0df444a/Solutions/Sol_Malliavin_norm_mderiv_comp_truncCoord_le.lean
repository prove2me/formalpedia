-- Prove2me | solution 1 for Malliavin.norm_mderiv_comp_truncCoord_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:23.480963+00:00
-- url     : https://prove2.me/submissions/8f37035c-5f6b-482f-8c05-a107766c97df

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_mderiv_comp_truncCoord
import Theorems.Thm_Malliavin_abs_deriv_cutoff_le


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : (Fin n → ℝ) → ℝ} (hφ : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (m : ℕ)
    (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖mderiv μ (fun y ↦ f (truncCoord m L y)) x‖ ≤
      φ (truncCoord m L x) * ∑ i, ‖ofDual μ (L i)‖ := by
  rw [mderiv_comp_truncCoord μ f hf m L x]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have h1 : |fderiv ℝ f (truncCoord m L x) (Pi.single i 1)| ≤ φ (truncCoord m L x) :=
    (abs_fderiv_single_le f _ i).trans (hφ _)
  have h0 : 0 ≤ φ (truncCoord m L x) := (abs_nonneg _).trans h1
  calc |fderiv ℝ f (truncCoord m L x) (Pi.single i 1)| * |deriv (cutoff m) (L i x)| *
        ‖ofDual μ (L i)‖
      ≤ φ (truncCoord m L x) * 1 * ‖ofDual μ (L i)‖ := by
        gcongr
        exact abs_deriv_cutoff_le m _
    _ = φ (truncCoord m L x) * ‖ofDual μ (L i)‖ := by ring
end Malliavin
