-- Prove2me | solution 1 for GlobalTheory.TorusExt.add_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:13:14.179793+00:00
-- url     : https://prove2.me/submissions/efd330a1-c22a-4817-a8e3-c4fe2ca4665f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorusExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
attribute [local instance] gtGroup
namespace GlobalTheory.TorusExt
theorem _root_.solution (g g' : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    charVal (g + g') χ y J * th D y J (cP D _ χ) g.b g'.b = charVal g χ y J * charVal g' χ y J := gtAdd_val g g' χ hJ
end GlobalTheory.TorusExt
