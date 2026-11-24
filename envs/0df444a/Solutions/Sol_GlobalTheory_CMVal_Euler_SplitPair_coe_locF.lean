-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.SplitPair.coe_locF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:29.381706+00:00
-- url     : https://prove2.me/submissions/8852e1f4-66e6-47dc-9305-f7cfbb1a13a2

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeCharUnramifiedInverseSplitPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler.SplitPair
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (locF P a ha : P.adicCompletion E) = iota a P := rfl
end GlobalTheory.CMVal.Euler.SplitPair
