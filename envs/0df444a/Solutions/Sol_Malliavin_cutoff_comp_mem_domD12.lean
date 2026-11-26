-- Prove2me | solution 1 for Malliavin.cutoff_comp_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:14.643416+00:00
-- url     : https://prove2.me/submissions/d1afbf61-14c3-4ffd-91d9-4630cc9915bc

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_cutoff_contDiff


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
variable {φ : ℝ → ℝ} {K : ℝ≥0}
namespace Malliavin
theorem _root_.solution (m : ℕ) {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    (memLp_comp_of_deriv_le μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) F).toLp _ ∈
        domD12 μ ∧
      mderivClosure μ
          ((memLp_comp_of_deriv_le μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) F).toLp _) =
        (memLp_deriv_smul_of_deriv_le μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) F
          (mderivClosure μ F)).toLp _ :=
  comp_mem_domD12 μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) hF
end Malliavin
