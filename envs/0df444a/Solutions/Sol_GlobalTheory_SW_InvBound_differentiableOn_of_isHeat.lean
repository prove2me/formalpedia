-- Prove2me | solution 1 for GlobalTheory.SW.InvBound.differentiableOn_of_isHeat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:37.506093+00:00
-- url     : https://prove2.me/submissions/664c1ce4-7a14-4e69-a2f7-db759697754f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCuspsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilActionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatSwdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SwdTendstoZeroAtCuspsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHighStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceInvariantNormBounded
import Theorems.Thm_GlobalTheory_SW_ExpSum_differentiableOn


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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.InvBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.InvBound
theorem _root_.solution {D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ} (hD : IsHeat Ψ D) :
    DifferentiableOn ℂ (fun Z : CF Ψ N N => D Z 0 0) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} := by
  have g : Differentiable ℂ (fun Z : CF Ψ N N => ((Z, 0, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N)) :=
    differentiable_id.prodMk (differentiable_const _)
  have := DifferentiableOn.comp (s := {Z : CF Ψ N N | (Z : CM Ψ N N) ∈ Hn Ψ N}) hD.1
    g.differentiableOn fun Z hZ => hZ
  exact this
end GlobalTheory.SW.InvBound
