-- Prove2me | solution 1 for GlobalTheory.Cartier.SecMaps.on
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:01.388654+00:00
-- url     : https://prove2.me/submissions/5983cc9e-f5a1-46ea-9296-2f0a6a3e874d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen

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
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
namespace SecMaps
theorem _root_.solution {A B : LB X} {w : LB.Iso A B} {a : A.Sec} {b : B.Sec} (h : SecMaps w a b)
    (p : B.ι) (q : A.ι) {W : X.Opens} (hp : W ≤ B.U p) (hq : W ≤ A.U q) :
    resG X hp (b.f p) = resG X (le_inf hp hq)
      (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) * resG X hq (a.f q) := by
  have := congrArg (resG X (le_inf hp hq)) (h (p, q))
  rwa [map_mul, resG_resG, resG_resG] at this
end SecMaps
end GlobalTheory.Cartier
