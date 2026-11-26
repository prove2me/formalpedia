-- Prove2me | solution 1 for Malliavin.IteratedIntegralFamily.IsBrownian.integral_two_boxKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:10.642349+00:00
-- url     : https://prove2.me/submissions/c59917f7-87c8-4e5d-b76f-38d9cc1ffc72

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_coeFn_incrementProductLp
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
namespace IteratedIntegralFamily.IsBrownian
theorem _root_.solution {J : IteratedIntegralFamily P}
    (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    J.integral 2 (boxKernel ![a, c] ![b, d]) = incrementProductLp hB a b c d := by
  apply Lp.ext
  have h := hJ.box 2 ![a, c] ![b, d] (fun i ↦ by fin_cases i <;> simp [hab, hcd])
    (fun i j hij ↦ by
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hij ⊢ <;>
        first | exact absurd hij (lt_irrefl _) | exact hbc | exact absurd hij (by decide))
  refine h.trans ?_
  refine (coeFn_incrementProductLp hB a b c d).symm.mono fun ω hω ↦ ?_
  rw [← hω]
  simp only [chainIntegral, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
end IteratedIntegralFamily.IsBrownian
end Malliavin
