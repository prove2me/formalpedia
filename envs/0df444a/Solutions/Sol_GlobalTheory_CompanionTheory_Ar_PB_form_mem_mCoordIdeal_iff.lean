-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.form_mem_mCoordIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:45.721791+00:00
-- url     : https://prove2.me/submissions/f25af93e-2ee6-4b01-9ba5-a67505736edd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTrdeg_mConeMap_of_isMultiHomog_42bb4e513f85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_mConeMap_of_isMultiHomog_507fb917434b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_mem_mCoordIdeal_of_aeval_eq_zero_09693c41a4b2


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
theorem _root_.solution (w : (Σ k, J k) → R) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∈ mCoordIdeal w ↔ MvPolynomial.aeval w g = 0 := by
  refine ⟨fun h => ?_, GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero w hg⟩
  have h' : mConeMap w g = 0 := h
  rw [GroundTheory.Heights₂.Heights.LowerBoundFree.mConeMap_of_isMultiHomog w hg] at h'
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact MvPolynomial.C_eq_zero.1 h1
  · exact absurd h1 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero _))
end GlobalTheory.CompanionTheory.Ar.PB
