-- Prove2me | solution 1 for GlobalTheory.CubeValues.val_pullU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:53.590191+00:00
-- url     : https://prove2.me/submissions/a28f5b31-65bb-469e-b12a-123c9979d43c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace

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
open GlobalTheory GlobalTheory.CubeValues
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.CubeValues
theorem _root_.solution (hv : ValueRules) {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)ˣ) :
    valAt' x (φ ⁻¹ᵁ U) (pullU φ U f).val = valAt' (x ≫ φ) U f.val :=
  (hv X x).2.2.2.1 Y φ U f.val
end GlobalTheory.CubeValues
