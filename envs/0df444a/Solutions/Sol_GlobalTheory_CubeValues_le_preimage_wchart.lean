-- Prove2me | solution 1 for GlobalTheory.CubeValues.le_preimage_wchart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:05.484884+00:00
-- url     : https://prove2.me/submissions/c1bd8fb5-0129-45a2-97d8-e81ed767f765

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
theorem _root_.solution {Y : Scheme.{0}} (L : LB Y) {K : Type} [Fintype K] (φ : K → (X ⟶ Y))
    (j : K → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ L.wchart φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  have key : ∀ q : Sp ℂ, q ∈ x ⁻¹ᵁ L.wchart φ j ↔ ∀ k, q ∈ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
    intro q
    show x q ∈ L.wchart φ j ↔ ∀ k, φ k (x q) ∈ L.U (j k)
    simp [LB.wchart]
  constructor
  · intro h k q _
    exact (key q).1 (h trivial) k
  · intro h q _
    exact (key q).2 (fun k => h k trivial)
end GlobalTheory.CubeValues
