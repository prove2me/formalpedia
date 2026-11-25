-- Prove2me | solution 1 for GlobalTheory.T.smooth_genericFibre_of_affine_opens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:24:35.607375+00:00
-- url     : https://prove2.me/submissions/5b1296c1-cf83-4063-9a46-aee838c06f11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGenericFibreOfAffineOpens
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGenericFibreOfAffineOpensStatement
import Theorems.Thm_GlobalTheory_smoothOfRelativeDimension_genericFibre_of_affine


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
open GlobalTheory.ZM
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (o : Type) [CommRing o] [IsDomain o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)))) → SmoothOfRelativeDimension d (pullback.snd s (spMap (algebraMap o (FractionRing o)))) := by
  first | exact @GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine | exact GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine | (intros; apply GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine <;> assumption)
end _root_.GlobalTheory.T
