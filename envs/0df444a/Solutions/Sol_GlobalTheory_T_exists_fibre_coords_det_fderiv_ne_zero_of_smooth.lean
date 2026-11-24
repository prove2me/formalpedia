-- Prove2me | solution 1 for GlobalTheory.T.exists_fibre_coords_det_fderiv_ne_zero_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:05.37221+00:00
-- url     : https://prove2.me/submissions/89723b23-d7a4-4e7f-aeb1-da96a010efd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoords
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoordsStatement
import Theorems.Thm_GlobalTheory_KS_exists_fibre_coords


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
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z, ∃ (W : X.Opens) (t : Fin P₀.g → Γ(X, W)), z ∈ dom u m W ∧ (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)).det ≠ 0 := by
  first | exact @GlobalTheory.KS.exists_fibre_coords | exact GlobalTheory.KS.exists_fibre_coords | (intros; apply GlobalTheory.KS.exists_fibre_coords <;> assumption)
end _root_.GlobalTheory.T
