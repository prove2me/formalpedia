-- Prove2me | solution 1 for GlobalTheory.ComplexPointsGroup.IsContFamily.continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:56:04.629597+00:00
-- url     : https://prove2.me/submissions/096196f3-2827-4f2c-adcd-905b4ad9c871

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsTopologicalGroupComplexPoints
import Theorems.Thm_GlobalTheory_ComplexPointsGroup_IsContFamily_isOpen_mem

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
open GlobalTheory GlobalTheory.ComplexPointsGroup
variable {T : Type} [TopologicalSpace T]
namespace GlobalTheory.ComplexPointsGroup
namespace IsContFamily
theorem _root_.solution {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (U : X.Opens)
    (f : Γ(X, U)) : ContinuousOn (fun t => valAt' (e t) U f) {t | ⊤ ≤ e t ⁻¹ᵁ U} :=
  (continuousOn_open_iff (he.isOpen_mem U)).2 fun O hO => he U f O hO
end IsContFamily
end GlobalTheory.ComplexPointsGroup
