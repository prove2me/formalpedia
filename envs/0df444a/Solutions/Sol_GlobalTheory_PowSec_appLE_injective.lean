-- Prove2me | solution 1 for GlobalTheory.PowSec.appLE_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:12.121556+00:00
-- url     : https://prove2.me/submissions/61eae2c8-a8ad-4466-8b94-da8e76f0f306

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections

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
open GlobalTheory GlobalTheory.PowSec
variable {X Y : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)
namespace GlobalTheory.PowSec
theorem _root_.solution [IsIso ρ] (U : Y.Opens) (V : X.Opens) (h : V = ρ ⁻¹ᵁ U) :
    Function.Injective (ρ.appLE U V h.le).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (ρ.app U)).1
end GlobalTheory.PowSec
