-- Prove2me | solution 1 for GlobalTheory.T.square_zero_neighbourhood_product_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:26.090516+00:00
-- url     : https://prove2.me/submissions/ef95a0f2-3e4a-40ba-a8a5-b6fb073fe23b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodProductZero
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodProductZeroStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FirstOrderNbhd_ideal_sq_zero


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (i' : Sp R ⟶ (e.ker ^ 2).subscheme), i' ≫ (e.ker ^ 2).subschemeι = e → ∀ a b : Γ((e.ker ^ 2).subscheme, ⊤), i'.appTop a = 0 → i'.appTop b = 0 → a * b = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FirstOrderNbhd.ideal_sq_zero | exact GlobalTheory.CompanionTheory.FirstOrderNbhd.ideal_sq_zero | (intros; apply GlobalTheory.CompanionTheory.FirstOrderNbhd.ideal_sq_zero <;> assumption)
end _root_.GlobalTheory.T
