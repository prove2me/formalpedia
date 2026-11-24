-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.not_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:24:15.523787+00:00
-- url     : https://prove2.me/submissions/472df6dc-1832-4f77-a914-55e373ef6967

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_over_iff_under


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution {w : HeightOneSpectrum (𝓞 E)} {v v' : HeightOneSpectrum (OF E)} (h : Over w v') (hne : v' ≠ v) : ¬ Over w v :=
  fun h' => hne (((over_iff_under _ _).1 h).symm.trans ((over_iff_under _ _).1 h'))
end GlobalTheory.CMVal.Euler
