-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.dualGram_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:47:43.103533+00:00
-- url     : https://prove2.me/submissions/dd180eef-8e11-4c05-ab71-1c7cc05ebf01

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_dualGram_inner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {Z : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over Z} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution {r : ℕ} {Γ Γ' : Matrix (Fin r) (Fin r) ℂ} (hΓ : Γ.IsHermitian) (h : Γ'ᵀ * Γ = 1)
    {y u : Fin r → ℂ} (hu : ∀ x, star u ⬝ᵥ Γ *ᵥ x = y ⬝ᵥ x) : star y ⬝ᵥ Γ' *ᵥ y = star u ⬝ᵥ Γ *ᵥ u :=
  dualGram_inner hΓ h hu hu
end GlobalTheory.CompanionTheory.Ar.PB
