-- Prove2me | solution 1 for GlobalTheory.SW.UnitaryLeft.thH_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:35:49.881774+00:00
-- url     : https://prove2.me/submissions/d9bee25c-03d0-4ed6-8228-71c16b2f3651

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_expo_mul
import Theorems.Thm_GlobalTheory_SW_Base_expo_mul
import Theorems.Thm_GlobalTheory_SW_HAct_left_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UnitaryLeft
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.UnitaryLeft
theorem _root_.solution {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    thH Ψ (fun x : Matrix (Fin n) (Fin N) E => φ (h * x)) Z z z' = thH Ψ φ Z (mv Ψ h z) (mv' Ψ h z') := by
  have hh' : h * ccT h = 1 := mul_eq_one_comm.1 hh
  let e : Matrix (Fin n) (Fin N) E ≃ Matrix (Fin n) (Fin N) E :=
    { toFun := fun x => h * x
      invFun := fun x => ccT h * x
      left_inv := fun x => by simp only [← Matrix.mul_assoc, hh, Matrix.one_mul]
      right_inv := fun x => by simp only [← Matrix.mul_assoc, hh', Matrix.one_mul] }
  unfold thH
  rw [← e.tsum_eq (fun x => φ x * cexp (2 * Real.pi * I * expo Ψ x Z (mv Ψ h z) (mv' Ψ h z')))]
  refine tsum_congr fun x => ?_
  change _ = φ (h * x) * cexp (2 * Real.pi * I * expo Ψ (h * x) Z (mv Ψ h z) (mv' Ψ h z'))
  rw [expo_mul Ψ hh]
end GlobalTheory.SW.UnitaryLeft
