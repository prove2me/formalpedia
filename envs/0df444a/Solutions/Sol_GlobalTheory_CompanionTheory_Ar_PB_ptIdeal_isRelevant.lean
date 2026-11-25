-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.ptIdeal_isRelevant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:00:27.283803+00:00
-- url     : https://prove2.me/submissions/036ddd14-ec46-4456-928c-0901101ae409

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_exists_ptIdeal_eq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_relevant_99031b883ef8


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
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) (q : Cpt ξ) :
    IsRelevant (ptIdeal ξ x q) := by
  obtain ⟨R, _, z, w, -, hw, e⟩ := exists_ptIdeal_eq h q
  rw [e]
  choose c hc using hw.1
  exact GroundTheory.Heights₂.Heights.CoordinateConeArithVar.relevant w c fun k => (hc k).ne_zero
end GlobalTheory.CompanionTheory.Ar.PB
