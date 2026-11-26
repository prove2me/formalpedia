-- Prove2me | solution 1 for Malliavin.contDiff_truncCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:28.818666+00:00
-- url     : https://prove2.me/submissions/71bf51be-48b1-4607-ba5f-1bb2e97ee8c2

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_cutoff_contDiff


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
namespace Malliavin
theorem _root_.solution (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) :
    ContDiff ℝ 1 (truncCoord m L) :=
  contDiff_pi.mpr fun i ↦ (cutoff_contDiff m).comp (L i).contDiff
end Malliavin
