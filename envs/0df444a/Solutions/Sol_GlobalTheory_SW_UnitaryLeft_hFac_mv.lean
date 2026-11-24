-- Prove2me | solution 1 for GlobalTheory.SW.UnitaryLeft.hFac_mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:02:47.365333+00:00
-- url     : https://prove2.me/submissions/17f29dc0-8897-45e0-af3e-1f51e4ae72fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_sum_rows_unitary
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_unit_map

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
    (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    hFac Ψ γ Z (mv Ψ h z) (mv' Ψ h z') = hFac Ψ γ Z z z' := by
  unfold hFac
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [mv, mv']
  rw [sum_rows_unitary _ _ (unit_map hh τ.1)]
end GlobalTheory.SW.UnitaryLeft
