-- Prove2me | solution 1 for GlobalTheory.Conv.halfCurve_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:00:06.051613+00:00
-- url     : https://prove2.me/submissions/01472774-e2e0-4390-ac54-80db3d4b4534

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_GlobalTheory_Conv_halfCurve_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {Z : Scheme.{0}}
namespace GlobalTheory.Conv
theorem _root_.solution {T T' : ℝ} (h : T ≤ T') (yT : Sp (halfRing T) ⟶ Z) {w : ℂ}
    (hw : T' < w.im) :
    halfCurve (spMap (Subalgebra.inclusion (halfRing_mono h) : halfRing T →+* halfRing T') ≫ yT) w =
      halfCurve yT w := by
  rw [halfCurve_eq _ hw, halfCurve_eq _ (h.trans_lt hw), ← Category.assoc, ← spMap_comp]
  rfl
end GlobalTheory.Conv
