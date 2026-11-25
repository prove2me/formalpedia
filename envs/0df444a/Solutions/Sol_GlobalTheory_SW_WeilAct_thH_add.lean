-- Prove2me | solution 1 for GlobalTheory.SW.WeilAct.thH_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:30.990869+00:00
-- url     : https://prove2.me/submissions/a8894090-5f94-4cdd-b90f-0db0e39b1af2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Theorems.Thm_GlobalTheory_T_hermitianTheta_summable_and_determines_testFn


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
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.WeilAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.WeilAct
theorem _root_.solution (hΨ : IsType Ψ) {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (z z' : CM Ψ n N) :
    thH Ψ (φ + ψ) Z z z' = thH Ψ φ Z z z' + thH Ψ ψ Z z z' := by
  have h1 := ((GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N φ hφ Z hZ).1 z z').of_norm
  have h2 := ((GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N ψ hψ Z hZ).1 z z').of_norm
  unfold thH
  rw [← h1.tsum_add h2]
  refine tsum_congr fun x => ?_
  simp only [Pi.add_apply, add_mul]
end GlobalTheory.SW.WeilAct
