-- Prove2me | solution 1 for Malliavin.indepFun_incr_incr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:26.699959+00:00
-- url     : https://prove2.me/submissions/785d9826-465e-482b-bf41-bbf5f11fb41b

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
theorem _root_.solution (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    IndepFun (fun ω ↦ B b ω - B a ω) (fun ω ↦ B d ω - B c ω) P := by
  have hmono : Monotone ![a, b, c, d] := by
    refine Fin.monotone_iff_le_succ.mpr ?_
    intro i
    fin_cases i <;> simp [hab, hbc, hcd]
  have := (hB.hasIndepIncrements 3 ![a, b, c, d] hmono).indepFun (i := 0) (j := 2) (by decide)
  simpa only [Fin.isValue, Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_zero,
    Fin.castSucc_zero, Fin.reduceSucc, Matrix.cons_val, Fin.reduceCastSucc] using this
end Malliavin
