-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.pairT_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:44:32.153164+00:00
-- url     : https://prove2.me/submissions/7f08cc47-8176-4575-bd09-e2d11bfbb288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Theorems.Thm_GlobalTheory_SW_HeisH_trace_eq
import Theorems.Thm_GlobalTheory_SW_Base_map_cc


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.HeisH
theorem _root_.solution (hΨ : IsType Ψ) (b x : Matrix (Fin n) (Fin N) E) :
    ((pairT b x : ℚ) : ℂ) = ∑ τ : Ψ, ((b.map τ.1 * (x.map τ.1)ᴴ).trace +
      (x.map τ.1 * (b.map τ.1)ᴴ).trace) := by
  rw [pairT, trace_eq hΨ]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [Matrix.trace, Matrix.mul_apply, Base.map_cc, mul_comm]
end GlobalTheory.SW.HeisH
