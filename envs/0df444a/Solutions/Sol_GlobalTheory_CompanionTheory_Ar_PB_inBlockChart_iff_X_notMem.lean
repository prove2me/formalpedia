-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.inBlockChart_iff_X_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:48:43.97338+00:00
-- url     : https://prove2.me/submissions/3a538642-59f4-461a-8001-93e6a35861f4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_inBlockChart_centre_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_ptIdeal_centre
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_exists_ptIdeal_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


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
theorem _root_.solution (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) (q : Cpt ξ)
    (c : ∀ k, J k) : InBlockChart ξ x c q ↔ ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ ptIdeal ξ x q := by
  obtain ⟨R, _, z, w, e, hw, -⟩ := exists_ptIdeal_eq h q
  have hz : genPt ξ ⤳ centre z := e ▸ q.2
  obtain rfl : q = ⟨centre z, hz⟩ := Subtype.ext e.symm
  rw [ptIdeal_centre hw hz, inBlockChart_centre_iff hw hz]
  refine forall_congr' fun k => not_congr ?_
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X, mul_eq_zero, MvPolynomial.C_eq_zero,
    or_iff_left (MvPolynomial.X_ne_zero _)]
end GlobalTheory.CompanionTheory.Ar.PB
