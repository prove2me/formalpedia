-- Prove2me | solution 1 for GlobalTheory.SW.Decay.coef_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:53.190937+00:00
-- url     : https://prove2.me/submissions/9889561c-50f3-432b-93bf-d93e6f104117

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
import Theorems.Thm_GlobalTheory_SW_Decay_volume_cube
import Theorems.Thm_GlobalTheory_SW_Decay_posDef_of_ge
import Theorems.Thm_GlobalTheory_SW_Decay_norm_integrand_le

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
variable {m : ℕ} {X : (Fin m → ℝ) → CM Ψ N N} {f : CM Ψ N N → ℂ} {T : Matrix (Fin N) (Fin N) E}
  {a : ℂ} {η B : ℝ}
namespace GlobalTheory.SW.Decay
theorem _root_.solution (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T) (hη : 0 < η)
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a) {Y : CM Ψ N N}
    (hY : ∀ τ, (Y τ - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) :
    ‖a‖ ≤ B * Real.exp (2 * π * ∑ τ : Ψ, (T.map τ.1 * Y τ).trace.re) := by
  rw [ha Y fun τ => posDef_of_ge hη (hY τ)]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cube m)
    (by rw [volume_cube]; exact ENNReal.one_lt_top)
    (fun x _ => norm_integrand_le hX hT hη hB hY x)
  simpa [Measure.real, volume_cube] using this
end GlobalTheory.SW.Decay
