-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.exists_ptIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:19.338797+00:00
-- url     : https://prove2.me/submissions/ac931b2a-4513-4295-84fb-7ae63a16f1fe

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_ptIdeal_centre
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_exists_inBlockChart
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_exists_coordsAt
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
theorem _root_.solution (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) (q : Cpt ξ) :
    ∃ (R : Type) (_ : Field R) (z : Spec (CommRingCat.of R) ⟶ Z) (w : (Σ k, J k) → R),
      centre z = q.1 ∧ CoordsAt ξ x z w ∧ ptIdeal ξ x q = mCoordIdeal w := by
  let z : Spec (CommRingCat.of (Z.residueField q.1)) ⟶ Z := Z.fromSpecResidueField q.1
  have e : centre z = q.1 := Scheme.fromSpecResidueField_apply _ _
  have hz : genPt ξ ⤳ centre z := by rw [e]; exact q.2
  have eq : q = ⟨centre z, hz⟩ := Subtype.ext e.symm
  obtain ⟨c, hc⟩ := exists_inBlockChart h ⟨centre z, hz⟩
  obtain ⟨w, hw⟩ := CoordModel.exists_coordsAt x hz (fun k => ⟨c k, hc k⟩) h.gen
  exact ⟨_, inferInstance, z, w, e, hw, (congrArg (ptIdeal ξ x) eq).trans (ptIdeal_centre hw hz)⟩
end GlobalTheory.CompanionTheory.Ar.PB
