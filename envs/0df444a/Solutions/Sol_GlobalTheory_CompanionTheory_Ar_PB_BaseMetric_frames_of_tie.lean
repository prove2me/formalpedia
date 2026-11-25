-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.BaseMetric.frames_of_tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:33:18.167626+00:00
-- url     : https://prove2.me/submissions/dbb6d4ef-b9ac-473f-bcea-caae297be7fc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_FlagTie_frames_centre

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
variable {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace BaseMetric
theorem _root_.solution {n : ℕ} (BM : BaseMetric M n) (tie : FlagTie M 𝔐) {i : Fin BM.q} {x : BM.Rb.X}
    (hx : x ∈ BM.O i) {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hz : CoordsAt 𝔐.ξ M.x z (BM.Rb.lift x x))
    (τ : CMType H) : (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame (BM.F i) τ) ⟨centre z, 𝔐.all _⟩ ∧
      (omBundle 𝔐 τ).IsFrameAt (tie.omFrame (BM.F i) τ) ⟨centre z, 𝔐.all _⟩ :=
  tie.frames_centre hz (BM.isFrame i) (BM.good i x hx) τ
end BaseMetric
end GlobalTheory.CompanionTheory.Ar.PB
