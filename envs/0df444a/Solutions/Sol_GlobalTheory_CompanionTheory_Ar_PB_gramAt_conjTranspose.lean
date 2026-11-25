-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.gramAt_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:29.078803+00:00
-- url     : https://prove2.me/submissions/729ceb7a-9fd8-4f1d-822e-e5a6aa8049b4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HodgeForm_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HodgeIP_conj


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
theorem _root_.solution {M : LieModel G ξ Li} {L : LB G.left} {z : Spec (CommRingCat.of ℂ) ⟶ Z} {r : ℕ}
    {b : Fin r → Li} {Γ : Matrix (Fin r) (Fin r) ℂ} (h : M.GramAt L z b Γ) : M.GramAt L z b Γᴴ :=
  let ⟨v, hv, h'⟩ := h
  ⟨v, hv, fun p q => (h' q p).conj⟩
end GlobalTheory.CompanionTheory.Ar.PB
