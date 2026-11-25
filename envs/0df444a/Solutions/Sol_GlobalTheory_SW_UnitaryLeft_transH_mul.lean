-- Prove2me | solution 1 for GlobalTheory.SW.UnitaryLeft.transH_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:26.817798+00:00
-- url     : https://prove2.me/submissions/e4576bb3-882d-4bcc-93d5-7c024b9b0207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_thH_mul
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_hFac_mv
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_mul_of_mulVec
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_mul_of_vecMul

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
theorem _root_.solution {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (γ : M2 E N)
    {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (H : TransH Ψ γ φ ψ) :
    TransH Ψ γ (fun x : Matrix (Fin n) (Fin N) E => φ (h * x))
      (fun x : Matrix (Fin n) (Fin N) E => ψ (h * x)) := by
  intro Z hZ z z'
  rw [thH_mul Ψ hh ψ, thH_mul Ψ hh φ, ← hFac_mv Ψ hh, ← H Z hZ]
  congr 1
  · funext τ; exact mul_of_mulVec _ _ _
  · funext τ; exact mul_of_vecMul _ _ _
end GlobalTheory.SW.UnitaryLeft
