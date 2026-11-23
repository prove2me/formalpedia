-- Prove2me | solution 1 for GlobalTheory.CMVal.CondExp.dvd_prod_primes_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:20.034435+00:00
-- url     : https://prove2.me/submissions/d2522095-fca6-47fd-8c8a-8e178a6f9ee1

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
    (Q : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R) :
    v.asIdeal ∣ ∏ q ∈ Q, q.asIdeal ↔ v ∈ Q := by
  constructor
  · intro h
    obtain ⟨q, hq, hd⟩ := (v.prime.dvd_finset_prod_iff _).1 h
    have : q.asIdeal = v.asIdeal :=
      q.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hd)
    rwa [← HeightOneSpectrum.ext this]
  · intro h
    exact Finset.dvd_prod_of_mem _ h
end GlobalTheory.CMVal.CondExp
