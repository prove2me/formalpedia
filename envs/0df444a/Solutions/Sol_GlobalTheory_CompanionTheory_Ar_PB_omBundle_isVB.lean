-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.omBundle_isVB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:48:09.392283+00:00
-- url     : https://prove2.me/submissions/207deeec-7f63-46eb-8a5f-47d90a138b8d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_isVBOn_dual_and_bidual
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_restrict_isVBOn


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
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S x) (τ : CMType H) : (omBundle 𝔐 τ).IsVB D.q ⊤ :=
  (Lat.isVBOn_dual_and_bidual _ _ _ _ _ _ _ (Lat.restrict_isVBOn _ _ _ _ _ _ _ _ (𝔐.vb (.inr τ))).1).1
end GlobalTheory.CompanionTheory.Ar.PB
