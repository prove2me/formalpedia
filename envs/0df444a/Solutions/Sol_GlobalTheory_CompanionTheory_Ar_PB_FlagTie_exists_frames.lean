-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.FlagTie.exists_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:18.13175+00:00
-- url     : https://prove2.me/submissions/742ad5b3-36e3-40ee-a70e-b56bb99d7563

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_exists_goodFrame

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
namespace FlagTie
theorem _root_.solution (tie : FlagTie M 𝔐) (q : Cpt 𝔐.ξ) :
    ∃ F, M.IsFrame F ∧ M.GoodAt F (ptIdeal 𝔐.ξ M.x q) ∧ ∀ τ,
      (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) q ∧ (omBundle 𝔐 τ).IsFrameAt (tie.omFrame F τ) q :=
  let ⟨F, h, h'⟩ := exists_goodFrame 𝔐 q
  ⟨F, h, h', fun τ => ⟨tie.frameW q F h h' τ, tie.frameO q F h h' τ⟩⟩
end FlagTie
end GlobalTheory.CompanionTheory.Ar.PB
