-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.closed_eq_univ_of_geomPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:21.477225+00:00
-- url     : https://prove2.me/submissions/169c74c4-c12a-4e66-9093-1e7ea5539316

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_exists_geomPoint_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {K : Type u} [Field K] [IsAlgClosed K]
namespace GlobalTheory.ComplexPoints
theorem _root_.solution {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] {Z : Set X} (hZ : IsClosed Z)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = t → ∃ a, x a ∈ Z) : Z = Set.univ := by
  by_contra hne
  obtain ⟨x, hx, hxZ⟩ := exists_geomPoint_mem p t hZ.isOpen_compl.isLocallyClosed
    (Set.nonempty_compl.mpr hne)
  obtain ⟨a, ha⟩ := h x hx
  exact hxZ a ha
end GlobalTheory.ComplexPoints
