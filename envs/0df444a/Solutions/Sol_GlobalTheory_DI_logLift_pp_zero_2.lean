-- Prove2me | solution 2 for GlobalTheory.DI.logLift_pp_zero
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T22:51:26.880594+00:00
-- url     : https://prove2.me/submissions/9168277e-f9ee-49f9-bce2-da8c0165544b

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

theorem solution (hπ : IsFlatLift p π) : (p : Kt) * p = 0 := by
  apply (hπ.ann _).2
  rw [map_natCast, CharP.cast_eq_zero K p]
