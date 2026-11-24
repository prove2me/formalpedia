-- Prove2me | solution 1 for GlobalTheory.T.isTotalCochainOfDegree_succ_of_differentials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:16:06.160544+00:00
-- url     : https://prove2.me/submissions/30c86ca9-d4e2-4c93-b158-5570ba196a79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTotalCochainOfDegreeSuccOfDifferentials
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTotalCochainOfDegreeSuccOfDifferentialsStatement
import Theorems.Thm_GlobalTheory_DI_inTot_delta_Dtot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → ∀ m c, InTot T m c → InTot T (m + 1) (delta c) ∧ ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → InTot T (m + 1) (Dtot d c)) := by
  first | exact @GlobalTheory.DI.inTot_delta_Dtot | exact GlobalTheory.DI.inTot_delta_Dtot | (intros; apply GlobalTheory.DI.inTot_delta_Dtot <;> assumption)
end _root_.GlobalTheory.T
