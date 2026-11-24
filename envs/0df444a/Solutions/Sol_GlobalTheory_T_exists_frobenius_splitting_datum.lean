-- Prove2me | solution 1 for GlobalTheory.T.exists_frobenius_splitting_datum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:08:08.399804+00:00
-- url     : https://prove2.me/submissions/1d83d146-5f48-42a4-a0ca-f26443315b54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_ExistsFrobeniusSplittingDatum
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_ExistsFrobeniusSplittingDatumStatement
import Theorems.Thm_GlobalTheory_DI_exists_isPhi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsDatum p d f h → ∃ Φ, IsPhi p f h Φ := by
  first | exact @_root_.GlobalTheory.DI.exists_isPhi | exact _root_.GlobalTheory.DI.exists_isPhi | (intros; apply _root_.GlobalTheory.DI.exists_isPhi <;> assumption)
end _root_.GlobalTheory.T
