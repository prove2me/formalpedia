-- Prove2me | solution 1 for Malliavin.symmetrizeL_iteratedKernelPurePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:25:06.125747+00:00
-- url     : https://prove2.me/submissions/7bed4dde-cea9-4ced-bd49-b351f8f5ebd9

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower
import Theorems.Thm_Malliavin_coeFn_iteratedKernelPurePower
import Theorems.Thm_Malliavin_isSymmetric_iteratedKernelPurePowerFun
import Theorems.Thm_Malliavin_symmetrizeL_eq_self_of_ae_symmetric


set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
namespace Malliavin
theorem _root_.solution (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
        (iteratedKernelPurePower n f) =
      iteratedKernelPurePower n f := by
  apply symmetrizeL_eq_self_of_ae_symmetric
  intro σ
  have hcoe := coeFn_iteratedKernelPurePower n f
  have hcomp := (measurePreserving_comp_perm nonnegativeLebesgueMeasure n σ
    ).quasiMeasurePreserving.ae_eq_comp hcoe
  filter_upwards [hcomp, hcoe] with t hcomp_t hcoe_t
  rw [hcomp_t, hcoe_t]
  exact isSymmetric_iteratedKernelPurePowerFun n f σ t
end Malliavin
