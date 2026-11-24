-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.smooth_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:25:52.999354+00:00
-- url     : https://prove2.me/submissions/700ba81c-33d7-4be8-b2ec-62e9cf8ac004

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution (A : Over (Sp R)) (g : ℕ) (hs : SmoothOfRelativeDimension g A.hom) :
    SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  have h₁ : SmoothOfRelativeDimension g (Limits.pullback.snd A.hom A.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hs
  rw [Over.tensorObj_hom, Limits.pullback.condition]
  exact smoothOfRelativeDimension_comp g g _ _
end GlobalTheory.CompanionTheory.AxForm
