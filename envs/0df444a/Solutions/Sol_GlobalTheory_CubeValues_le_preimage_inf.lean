-- Prove2me | solution 1 for GlobalTheory.CubeValues.le_preimage_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:29.113339+00:00
-- url     : https://prove2.me/submissions/a6f33b1c-5cfc-48c7-a01a-27450515450c

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
theorem _root_.solution (U V : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) ↔ ⊤ ≤ x ⁻¹ᵁ U ∧ ⊤ ≤ x ⁻¹ᵁ V := by
  show ⊤ ≤ x ⁻¹ᵁ U ⊓ x ⁻¹ᵁ V ↔ _
  exact le_inf_iff
end GlobalTheory.CubeValues
