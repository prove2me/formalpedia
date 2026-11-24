-- Prove2me | solution 1 for GlobalTheory.DI.FiltVanish.inTot_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:19.468496+00:00
-- url     : https://prove2.me/submissions/2f7dada0-66f7-4473-943b-09d25264856d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTotalCochainOfDegreeSuccOfDifferentialsStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_CechVanishingAlongFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.FiltVanish
variable {ι : Type} {E : Type} [AddCommGroup E]
namespace GlobalTheory.DI.FiltVanish
theorem _root_.solution (T : ℕ → Finset ι → AddSubgroup E) (m : ℕ) : InTot T m (0 : Finset ι → E) :=
  ⟨rfl, fun q s _ => (T q s).zero_mem, fun _ _ => rfl⟩
end GlobalTheory.DI.FiltVanish
