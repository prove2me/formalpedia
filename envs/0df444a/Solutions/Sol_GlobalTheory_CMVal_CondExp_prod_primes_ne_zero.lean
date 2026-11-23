-- Prove2me | solution 1 for GlobalTheory.CMVal.CondExp.prod_primes_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:26.282382+00:00
-- url     : https://prove2.me/submissions/e530987c-8e82-43ab-aed8-423d71d21e86

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConductorTimesSplitPrimesExponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.CondExp
namespace GlobalTheory.CMVal.CondExp
theorem _root_.solution {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) : ∏ q ∈ Q, q.asIdeal ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot
end GlobalTheory.CMVal.CondExp
