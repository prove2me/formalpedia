-- Prove2me | solution 1 for GlobalTheory.TorsionCompare.substJ_zR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:31:16.612806+00:00
-- url     : https://prove2.me/submissions/76891b7b-4889-4671-af07-a49c6406803d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R]
namespace GlobalTheory.TorsionCompare
theorem _root_.solution {n d : ℕ} (m : ℕ) (φ : Fin d → PS R n d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (q : Fin 1 × Fin d) :
    substJ m φ hφ (zR m q) = psJet m (φ q.2) := by
  exact MvPolynomial.aeval_X _ _
end GlobalTheory.TorsionCompare
