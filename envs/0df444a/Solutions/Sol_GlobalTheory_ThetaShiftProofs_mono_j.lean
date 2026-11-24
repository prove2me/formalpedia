-- Prove2me | solution 1 for GlobalTheory.ThetaShiftProofs.mono_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:32:57.282805+00:00
-- url     : https://prove2.me/submissions/e7452787-c88d-4600-827c-7a1b84a0ed02

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsOpenImmersionJKPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaShiftProofs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
namespace GlobalTheory.ThetaShiftProofs
theorem _root_.solution {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (hm : Mono (spMap β)) : Mono Y.j := by
  have := Y.jQ_open
  unfold Model.j; infer_instance
end GlobalTheory.ThetaShiftProofs
