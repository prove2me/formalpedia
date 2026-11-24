-- Prove2me | solution 1 for GlobalTheory.DI.logLift_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:09:26.67398+00:00
-- url     : https://prove2.me/submissions/3a52c38d-7780-4fdd-bb5b-bc958de47a1c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogLiftPpZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
variable {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K)
  {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (A : Subring K)
omit [Fact p.Prime]
namespace GlobalTheory.DI
theorem _root_.solution : LogLift p π F s (A : Set K) 1 :=
  ⟨1, map_one π, fun i _ => ⟨0, by simp [A.zero_mem], by simp⟩⟩
end GlobalTheory.DI
