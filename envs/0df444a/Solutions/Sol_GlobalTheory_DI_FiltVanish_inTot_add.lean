-- Prove2me | solution 1 for GlobalTheory.DI.FiltVanish.inTot_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:17.984961+00:00
-- url     : https://prove2.me/submissions/9cf1ac22-e429-4e63-8b51-a0c78bdc41ee

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
theorem _root_.solution {T : ℕ → Finset ι → AddSubgroup E} {m : ℕ} {c c' : Finset ι → E}
    (h1 : InTot T m c) (h2 : InTot T m c') : InTot T m (c + c') := by
  refine ⟨?_, ?_, ?_⟩
  · simp [h1.1, h2.1]
  · intro q s hq; exact (T q s).add_mem (h1.2.1 q s hq) (h2.2.1 q s hq)
  · intro s hs; simp [h1.2.2 s hs, h2.2.2 s hs]
end GlobalTheory.DI.FiltVanish
