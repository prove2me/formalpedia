-- Prove2me | solution 1 for GlobalTheory.RationalPoint.continuous_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:18.199808+00:00
-- url     : https://prove2.me/submissions/d7e88a65-a3b8-4a67-bd07-0c1b31832936

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology
open GlobalTheory
open GlobalTheory.RationalPoint
variable {k : Type} [Field k]
namespace GlobalTheory.RationalPoint
theorem _root_.solution {X Y : Over (Sp k)} (f : X ⟶ Y) :
    Continuous[zariski X, zariski Y] fun y => y ≫ f := by
  letI := zariski X
  letI := zariski Y
  exact continuous_induced_rng.2 (f.left.continuous.comp continuous_induced_dom)
end GlobalTheory.RationalPoint
