-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.top_le_preimage_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:06.77913+00:00
-- url     : https://prove2.me/submissions/f5f7af3c-c0d4-430a-b66e-2dc2d17d7044

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed

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
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {K : Type u} [Field K] [IsAlgClosed K]
namespace GlobalTheory.ComplexPoints
namespace _root_.GlobalTheory.ComplexPoints
theorem _root_.solution {L : Type u} [Field L] {X : Scheme.{u}}
    (x : Spec (.of L) ⟶ X) (U : X.Opens) (a : ↥(Spec (.of L))) : ⊤ ≤ x ⁻¹ᵁ U ↔ x a ∈ U := by
  constructor
  · intro h
    exact h (show a ∈ (⊤ : (Spec (.of L)).Opens) from trivial)
  · intro h b _
    rw [Subsingleton.elim b a]
    exact h
end _root_.GlobalTheory.ComplexPoints
end GlobalTheory.ComplexPoints
