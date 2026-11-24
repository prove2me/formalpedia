-- Prove2me | solution 1 for GlobalTheory.T.exists_local_chart_at_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:04.608884+00:00
-- url     : https://prove2.me/submissions/0653a3fe-de19-4f85-90dd-312038293948

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLocalChartAtPrime
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLocalChartAtPrimeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CotChart_exists_smooth_chart


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (g : ℕ), e ≫ s = 𝟙 _ → SmoothOfRelativeDimension g s → ∀ p : PrimeSpectrum R, ∃ (r : R) (A C : Type) (_ : CommRing A) (_ : CommRing C) (_ : Algebra C A) (_ : Algebra A (Localization.Away r)) (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R), r ∉ p.asIdeal ∧ IsOpenImmersion j ∧ Mono k ∧ j ≫ s = spMap (algebraMap C A) ≫ k ∧ spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e ∧ Module.Free A (KaehlerDifferential C A) ∧ Module.Finite A (KaehlerDifferential C A) ∧ Module.finrank A (KaehlerDifferential C A) = g := by
  first | exact @GlobalTheory.CompanionTheory.CotChart.exists_smooth_chart | exact GlobalTheory.CompanionTheory.CotChart.exists_smooth_chart | (intros; apply GlobalTheory.CompanionTheory.CotChart.exists_smooth_chart <;> assumption)
end _root_.GlobalTheory.T
