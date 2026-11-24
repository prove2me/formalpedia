-- Prove2me | solution 1 for GlobalTheory.SW.Decay.rpow_mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:40.483488+00:00
-- url     : https://prove2.me/submissions/d729ff19-6c2e-4c2f-88f6-e6d7ec93195f

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
theorem _root_.solution {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) :
    ∃ C : ℝ, ∀ u : ℝ, 0 < u → u ^ p * Real.exp (-(b * u)) ≤ C := by
  refine ⟨Real.exp (-(p * Real.log (b / (p + 1)))), fun u hu => ?_⟩
  have hε : 0 < b / (p + 1) := by positivity
  rw [Real.rpow_def_of_pos hu, ← Real.exp_add, Real.exp_le_exp]
  have h1 := Real.log_le_sub_one_of_pos (mul_pos hε hu)
  rw [Real.log_mul hε.ne' hu.ne'] at h1
  have h2 : p * (b / (p + 1) * u) ≤ b * u := by
    rw [← mul_assoc]
    gcongr
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hp]
end GlobalTheory.SW.Decay
