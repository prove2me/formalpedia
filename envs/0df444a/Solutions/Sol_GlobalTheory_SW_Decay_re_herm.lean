-- Prove2me | solution 1 for GlobalTheory.SW.Decay.re_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:39.668638+00:00
-- url     : https://prove2.me/submissions/9279e9bd-b77b-4129-b88b-b53a3b83632f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTubeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCusps

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Decay
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {N : ℕ}
namespace GlobalTheory.SW.Decay
theorem _root_.solution (Z : Matrix (Fin N) (Fin N) ℂ) : (Z - I • imH Z).IsHermitian := by
  have : Z - I • imH Z = (2 : ℂ)⁻¹ • (Z + Zᴴ) := by
    ext a b
    simp only [imH, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    field_simp
    ring
  rw [this, Matrix.IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose,
    add_comm]
  simp
end GlobalTheory.SW.Decay
