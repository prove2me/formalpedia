-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.surjective_of_complexPoints_lift_of_universallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:38:58.703722+00:00
-- url     : https://prove2.me/submissions/6818ff0e-c663-4acc-a088-1cdd594d00a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_surjective_of_complexPoints_lift

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
theorem _root_.solution {k : Type} [Field k] (σ : k →+* ℂ)
    {A B : Scheme.{0}} (a : A ⟶ Sp k) [LocallyOfFiniteType a] [IsSeparated a] (b : B ⟶ Sp k)
    [UniversallyClosed b] (ψ : B ⟶ A) (hw : ψ ≫ a = b)
    (h : ∀ x : Sp ℂ ⟶ A, x ≫ a = spMap σ → ∃ y : Sp ℂ ⟶ B, y ≫ ψ = x) : Surjective ψ := by
  subst hw
  have : UniversallyClosed ψ := UniversallyClosed.of_comp_of_isSeparated ψ a
  exact surjective_of_complexPoints_lift σ a ψ ψ.isClosedMap.isClosed_range h
end GlobalTheory.ComplexPoints
