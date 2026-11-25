-- Prove2me | solution 1 for GlobalTheory.SW.Decay.norm_integrand_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:14:45.400261+00:00
-- url     : https://prove2.me/submissions/4fb130dc-eda3-4f09-93d4-26acff74f427

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
import Theorems.Thm_GlobalTheory_SW_Decay_imH_xy
import Theorems.Thm_GlobalTheory_SW_Decay_pr_im
import Theorems.Thm_P2M_GlobalTheory_SW_Decay_norm_e__f0075b22bc10
import Theorems.Thm_GlobalTheory_SW_Decay_posDef_of_ge

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
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) {Y : CM Ψ N N}
    (hY : ∀ τ, (Y τ - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) (x : Fin m → ℝ) :
    ‖f (fun τ => X x τ + I • Y τ) * cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y τ)))‖ ≤
      B * Real.exp (2 * π * ∑ τ : Ψ, (T.map τ.1 * Y τ).trace.re) := by
  have hi : ∀ τ, imH (X x τ + I • Y τ) = Y τ := fun τ =>
    imH_xy (hX x τ) (posDef_of_ge hη (hY τ)).1
  rw [norm_mul, norm_e', pr_im hT]
  simp only [hi]
  gcongr
  exact hB _ fun τ => by simpa only [hi] using hY τ
end GlobalTheory.SW.Decay
