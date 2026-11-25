-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.exists_goodFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:46.519862+00:00
-- url     : https://prove2.me/submissions/8324eeab-e333-4769-908d-8fd5d2ecf5fe

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_mCoordIdeal_le_ptIdeal
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_ptIdeal_isPrime
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_ptIdeal_isRelevant

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
theorem _root_.solution (𝔐 : HodgeCpt Y S M.x) (q : Cpt 𝔐.ξ) :
    ∃ F, M.IsFrame F ∧ M.GoodAt F (ptIdeal 𝔐.ξ M.x q) :=
  M.frames _ (ptIdeal_isPrime 𝔐.tie q) (ptIdeal_isRelevant 𝔐.tie q) (mCoordIdeal_le_ptIdeal _ _ q)
end GlobalTheory.CompanionTheory.Ar.PB
