-- Prove2me | solution 1 for GlobalTheory.T.vector_bundle_of_local_freeness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:36:03.947736+00:00
-- url     : https://prove2.me/submissions/18fcf4c7-75b8-4924-8b6f-25a43254751c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VectorBundleOfLocalFreeness
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VectorBundleOfLocalFreenessStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Cot_vb_of_free_on_basicOpens


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
theorem _root_.solution : ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (g : ℕ), (∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) ∧ Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) ∧ Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] W) = g) → VB R W g := by
  first | exact @GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens | exact GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens | (intros; apply GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens <;> assumption)
end _root_.GlobalTheory.T
