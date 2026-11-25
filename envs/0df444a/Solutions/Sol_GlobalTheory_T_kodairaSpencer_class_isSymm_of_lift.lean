-- Prove2me | solution 1 for GlobalTheory.T.kodairaSpencer_class_isSymm_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:28.106547+00:00
-- url     : https://prove2.me/submissions/ba1bae74-42c5-4c30-8389-486c7122335e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassIsSymmOfLift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassIsSymmOfLiftStatement
import Theorems.Thm_GlobalTheory_KS_isSymm_of_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ L : LB X, L.IsLB → LBIso P₀.L (L.pull m) → IsSymm Hm Θ := by
  first | exact @GlobalTheory.KS.isSymm_of_lift | exact GlobalTheory.KS.isSymm_of_lift | (intros; apply GlobalTheory.KS.isSymm_of_lift <;> assumption)
end _root_.GlobalTheory.T
