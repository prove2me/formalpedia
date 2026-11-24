-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.surjective_of_complexPoints_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:18:05.212799+00:00
-- url     : https://prove2.me/submissions/ecd54399-3de3-42ab-8bc6-2b7a6275fee3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_surjective_specMap_field
import Theorems.Thm_GlobalTheory_ComplexPoints_surjective_of_geomPoints_lift

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
variable {X Y : Scheme.{0}}
namespace GlobalTheory.ComplexPoints
theorem _root_.solution {k : Type} [Field k] (σ : k →+* ℂ) {A B : Scheme.{0}}
    (a : A ⟶ Sp k) [LocallyOfFiniteType a] (ψ : B ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp ℂ ⟶ A, x ≫ a = spMap σ → ∃ y : Sp ℂ ⟶ B, y ≫ ψ = x) : Surjective ψ :=
  haveI : Surjective (spMap σ) := surjective_specMap_field σ
  surjective_of_geomPoints_lift a (spMap σ) ψ hψ h
end GlobalTheory.ComplexPoints
