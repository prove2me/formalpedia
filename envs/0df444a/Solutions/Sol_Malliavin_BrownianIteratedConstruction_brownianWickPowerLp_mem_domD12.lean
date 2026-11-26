-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:11.466804+00:00
-- url     : https://prove2.me/submissions/f8560ba2-cd4a-4f79-bc73-5f69f7325476

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianStepDual_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_coeFn_brownianWickPowerLp
import Theorems.Thm_Malliavin_cylinder_expGrowth_mem_domD12
import Theorems.Thm_P2M_Malliavin_abs_polynomial_deriv_le__df93b7f4181a


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n ∈ domD12 P := by
  let p := varianceHermite (‖stepToLp v‖ ^ 2) n
  let F : (Fin 1 → ℝ) → ℝ := fun y ↦ p.eval (y 0)
  let L : Fin 1 → StrongDual ℝ W := fun _ ↦ brownianStepDual coordinate v
  let C := coeffMass p + coeffMass p.derivative
  let c : ℝ := p.natDegree
  have hC : 0 ≤ C := add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hF : ContDiff ℝ 1 F := contDiff_oneCoord (contDiff_polynomial_eval p)
  have hbound : ∀ y, |F y| ≤ C * Real.exp (c * ‖y‖) := by
    intro y
    exact abs_oneCoord_le hC hc (abs_polynomial_eval_le' p) y
  have hbound' : ∀ y, ‖fderiv ℝ F y‖ ≤ C * Real.exp (c * ‖y‖) := by
    intro y
    exact norm_fderiv_oneCoord_le (contDiff_polynomial_eval p) hC hc
      (abs_polynomial_deriv_le' p) y
  have hmem := (cylinder_expGrowth_mem_domD12 P hF hC hc hbound hbound' L).1
  have heq :
      (memLp_cylinder_expGrowth P hF hC hc hbound L).toLp _ =
        brownianWickPowerLp hB v n := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
        (memLp_cylinder_expGrowth P hF hC hc hbound L),
      coeFn_brownianWickPowerLp hB v n] with w hleft hright
    rw [hleft, hright]
    exact congrArg p.eval (brownianStepDual_apply coordinate coordinate_apply v w)
  rwa [heq] at hmem
end Malliavin.BrownianIteratedConstruction
