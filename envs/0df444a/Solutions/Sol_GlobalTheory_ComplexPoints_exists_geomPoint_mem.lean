-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.exists_geomPoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:19.00779+00:00
-- url     : https://prove2.me/submissions/430f2a9e-80d5-495c-8cc6-a1abe21950d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_exists_point_mem

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
    (t : Spec (.of K) ⟶ S) [Surjective t]
    {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = t ∧ ∀ a, x a ∈ Z := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨w, hw⟩ := (pullback.fst p t).surjective z
  obtain ⟨y, hy, hyZ⟩ := exists_point_mem (pullback.snd p t)
    (hZ.preimage (pullback.fst p t).continuous) ⟨w, show pullback.fst p t w ∈ Z from hw ▸ hz⟩
  refine ⟨y ≫ pullback.fst p t, ?_, fun a => hyZ a⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hy]
end GlobalTheory.ComplexPoints
