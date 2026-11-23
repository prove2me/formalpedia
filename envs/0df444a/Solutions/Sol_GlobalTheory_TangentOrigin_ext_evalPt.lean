-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.ext_evalPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:23.633792+00:00
-- url     : https://prove2.me/submissions/6de6ef2e-c4cd-4c5c-a62a-1643aca6ef7f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spec_fromSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
namespace GlobalTheory.TangentOrigin
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) {x y : Sp R ⟶ X} (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) (e : evalPt x U hx = evalPt y U hy) : x = y := by
  exact (eq_spec_fromSpec hU x hx).trans (e ▸ (eq_spec_fromSpec hU y hy).symm)
end GlobalTheory.TangentOrigin
