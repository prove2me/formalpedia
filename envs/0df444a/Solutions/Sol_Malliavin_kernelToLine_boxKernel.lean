-- Prove2me | solution 1 for Malliavin.kernelToLine_boxKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:52:14.052803+00:00
-- url     : https://prove2.me/submissions/5d63b189-1960-4ec6-9186-9c680b66d194

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution {a b : ℝ≥0} :
    kernelToLine (boxKernel (fun _ : Fin 1 ↦ a) (fun _ ↦ b)) =
      indicatorConstLp 2 measurableSet_Ioc (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ) := by
  have hset : (MeasurableEquiv.funUnique (Fin 1) ℝ≥0).symm ⁻¹'
      orderedBox (fun _ : Fin 1 ↦ a) (fun _ ↦ b) = Set.Ioc a b := by
    ext t
    simp only [MeasurableEquiv.funUnique_symm_apply, orderedBox, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      uniqueElim_const, Set.mem_Ioc, forall_const]
  unfold kernelToLine boxKernel
  change Lp.compMeasurePreserving _ measurePreserving_funUnique_symm_nnreal _ = _
  rw [Lp.indicatorConstLp_compMeasurePreserving]
  congr 1
end Malliavin
