-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.eq_exp_neg_one_of_le_of_not_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:27.806032+00:00
-- url     : https://prove2.me/submissions/80c3e3e2-a7da-4d5f-9228-698a1b21f771

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniformiserSplitPlaceCmOrderNonunit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution {g : WithZero (Multiplicative ℤ)} (h1 : g ≤ WithZero.exp (-1 : ℤ))
    (h2 : ¬ g ≤ WithZero.exp (-2 : ℤ)) : g = WithZero.exp (-1 : ℤ) := by
  have h0 : g ≠ 0 := fun h => h2 (h ▸ zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  omega
end GlobalTheory.CMVal.Euler
