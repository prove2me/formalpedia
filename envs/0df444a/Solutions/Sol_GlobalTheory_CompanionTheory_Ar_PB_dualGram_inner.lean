-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.dualGram_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:44.460072+00:00
-- url     : https://prove2.me/submissions/4079258a-d679-4cb6-aef1-f846f986507a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback

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
    {y y' u u' : Fin r → ℂ} (hu : ∀ x, star u ⬝ᵥ Γ *ᵥ x = y ⬝ᵥ x) (hu' : ∀ x, star u' ⬝ᵥ Γ *ᵥ x = y' ⬝ᵥ x) :
    star y ⬝ᵥ Γ' *ᵥ y' = star u' ⬝ᵥ Γ *ᵥ u := by
  have rep : ∀ {y u : Fin r → ℂ}, (∀ x, star u ⬝ᵥ Γ *ᵥ x = y ⬝ᵥ x) → star u ᵥ* Γ = y := fun {y u} hu =>
    dotProduct_eq _ _ fun x => by rw [← Matrix.dotProduct_mulVec, hu]
  have h1 : Γ' *ᵥ y' = star u' := by
    rw [← rep hu', ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, mul_eq_one_comm.1 h, Matrix.vecMul_one]
  have h2 : star y = Γ *ᵥ u := by
    rw [← rep hu, Matrix.star_vecMul, star_star, hΓ.eq]
  rw [h1, h2, dotProduct_comm]
end GlobalTheory.CompanionTheory.Ar.PB
