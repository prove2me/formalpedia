-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.opens_le_of_geomPoints
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:18.895803+00:00
-- url     : https://prove2.me/submissions/cf02ceb7-b74b-4722-9305-1b9881fda6fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_exists_geomPoint_mem
import Theorems.Thm_GlobalTheory_ComplexPoints_top_le_preimage_iff

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
    (t : Spec (.of K) ⟶ S) [Surjective t] (U V : X.Opens)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = t → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  intro z hzU
  by_contra hzV
  obtain ⟨x, hx, hxZ⟩ := exists_geomPoint_mem p t (Z := (U : Set X) ∩ (V : Set X)ᶜ)
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨z, hzU, hzV⟩
  let a : ↥(Spec (.of K)) := IsLocalRing.closedPoint K
  exact (hxZ a).2 ((top_le_preimage_iff x V a).1 (h x hx ((top_le_preimage_iff x U a).2 (hxZ a).1)))
end GlobalTheory.ComplexPoints
