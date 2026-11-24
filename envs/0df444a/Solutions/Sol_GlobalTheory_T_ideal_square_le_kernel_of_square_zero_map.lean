-- Prove2me | solution 1 for GlobalTheory.T.ideal_square_le_kernel_of_square_zero_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:11.550099+00:00
-- url     : https://prove2.me/submissions/11405141-abaa-4ac6-97f9-ff6ea066126d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMap
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMapStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CotKer_ker_sq_le_ker


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
theorem _root_.solution : ∀ (R Q B : Type) [CommRing R] [CommRing Q] [CommRing B] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ U), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → e.ker ^ 2 ≤ y.ker := by
  first | exact @GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker | exact GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker | (intros; apply GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker <;> assumption)
end _root_.GlobalTheory.T
