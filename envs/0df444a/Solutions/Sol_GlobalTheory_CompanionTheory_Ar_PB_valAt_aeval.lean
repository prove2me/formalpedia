-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.valAt_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:55.274329+00:00
-- url     : https://prove2.me/submissions/2edfd55d-9797-48b4-9c57-0c037b386074

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_valAt_mul


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
variable {Z : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
variable {ξ : Spec (CommRingCat.of Ω) ⟶ Z} {x : (Σ k, J k) → Ω} {R : Type} [Field R]
  {z : Spec (CommRingCat.of R) ⟶ Z} {w : (Σ k, J k) → R}
omit [Fintype K] [∀ k, Fintype (J k)]
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution {σ : Type} {a : σ → Ω} {r : σ → R} (hz : genPt ξ ⤳ centre z) (h : ∀ p, ValAt ξ z (a p) (r p))
    (s : MvPolynomial σ ℤ) : ValAt ξ z (MvPolynomial.aeval a s) (MvPolynomial.aeval r s) := by
  induction s using MvPolynomial.induction_on with
  | C n => exact ⟨hz, n, by simp, (map_intCast (Scheme.stalkClosedPointTo z).hom n).trans (by simp)⟩
  | add p q hp hq =>
    obtain ⟨_, x, hx, hx'⟩ := hp
    obtain ⟨_, y, hy, hy'⟩ := hq
    exact ⟨hz, x + y, by rw [map_add, map_add, hx, hy],
      (map_add (Scheme.stalkClosedPointTo z).hom x y).trans (by rw [map_add, ← hx', ← hy']; rfl)⟩
  | mul_X p i hp => simpa using CoordModel.valAt_mul hp (h i)
end GlobalTheory.CompanionTheory.Ar.PB
