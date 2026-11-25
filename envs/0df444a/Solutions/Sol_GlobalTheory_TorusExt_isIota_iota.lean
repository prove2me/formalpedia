-- Prove2me | solution 1 for GlobalTheory.TorusExt.isIota_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:51:51.632536+00:00
-- url     : https://prove2.me/submissions/b1f566ca-bbbc-4ba1-a22b-641f334b1eb6

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
theorem _root_.solution (hB : D.TauBimult) (x : D.X) : GtPtF.IsIota x (iota hB F x) := (exists_iota hB x).choose_spec
end GlobalTheory.TorusExt
