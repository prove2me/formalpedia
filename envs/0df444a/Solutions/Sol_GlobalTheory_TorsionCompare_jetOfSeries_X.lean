-- Prove2me | solution 1 for GlobalTheory.TorsionCompare.jetOfSeries_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:33:04.327847+00:00
-- url     : https://prove2.me/submissions/506ba967-0223-4ed5-a1d7-19c6899001a3

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
theorem _root_.solution {κ : Type} [Finite κ] (m : ℕ) (q : κ) :
    jetOfSeries m (MvPowerSeries.X q : MvPowerSeries κ R) = zR m q := by
  unfold jetOfSeries
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
  intro x hx
  rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ hx, ← MvPolynomial.coe_X,
    MvPolynomial.coeff_coe, sub_self]
end GlobalTheory.TorsionCompare
