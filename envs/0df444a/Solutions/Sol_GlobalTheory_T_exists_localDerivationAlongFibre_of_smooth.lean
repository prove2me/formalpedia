-- Prove2me | solution 1 for GlobalTheory.T.exists_localDerivationAlongFibre_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:38:40.805881+00:00
-- url     : https://prove2.me/submissions/b5a43bd1-5a42-4e6a-851a-264f7cb9f159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationAlongFibreOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationAlongFibreOfSmoothStatement
import Theorems.Thm_GlobalTheory_KS_exists_locDer_of_smooth


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDer x₀ D → IsAffineOpen W₀ → ∃ d, LocDer q p m D W₀ d := by
  first | exact @GlobalTheory.KS.exists_locDer_of_smooth | exact GlobalTheory.KS.exists_locDer_of_smooth | (intros; apply GlobalTheory.KS.exists_locDer_of_smooth <;> assumption)
end _root_.GlobalTheory.T
