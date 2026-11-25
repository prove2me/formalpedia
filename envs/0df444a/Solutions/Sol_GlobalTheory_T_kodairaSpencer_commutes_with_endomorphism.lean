-- Prove2me | solution 1 for GlobalTheory.T.kodairaSpencer_commutes_with_endomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:00:22.571442+00:00
-- url     : https://prove2.me/submissions/c010ef60-086c-4594-bf67-07c414cdea72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerCommutesWithEndomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerCommutesWithEndomorphismStatement
import Theorems.Thm_GlobalTheory_KS_Endo_comm_of_endo


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
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ (f : X ⟶ X) (f₀ : P₀.A ⟶ P₀.A) (F : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm Θ F := by
  first | exact @GlobalTheory.KS.Endo.comm_of_endo | exact GlobalTheory.KS.Endo.comm_of_endo | (intros; apply GlobalTheory.KS.Endo.comm_of_endo <;> assumption)
end _root_.GlobalTheory.T
