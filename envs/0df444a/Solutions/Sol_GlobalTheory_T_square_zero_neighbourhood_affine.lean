-- Prove2me | solution 1 for GlobalTheory.T.square_zero_neighbourhood_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:39:04.19845+00:00
-- url     : https://prove2.me/submissions/41d7853e-5137-4543-8178-3655a7f31a16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodAffine
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodAffineStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SectionNbhd_isAffine_subscheme_ker_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (t : U ⟶ Sp R) (e : Sp R ⟶ U) [IsClosedImmersion e], e ≫ t = 𝟙 _ → IsAffine (e.ker ^ 2).subscheme := by
  first | exact @GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq | exact GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq | (intros; apply GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq <;> assumption)
end _root_.GlobalTheory.T
