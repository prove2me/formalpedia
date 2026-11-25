-- Prove2me | solution 1 for GlobalTheory.TorusExt.iota_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:21.505991+00:00
-- url     : https://prove2.me/submissions/4bf09d59-63e7-4b7d-93ea-6920de2495f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Theorems.Thm_GlobalTheory_TorusExt_isIota_iota

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
theorem _root_.solution (hB : D.TauBimult) (x χ : D.X) {y J} (hJ : Good D.P.L y J) :
    charVal (iota hB F x) χ y J = tauVal D F x χ y J := ((isIota_iff_val _ _).1 (isIota_iota hB x)).2 χ y J hJ
end GlobalTheory.TorusExt
