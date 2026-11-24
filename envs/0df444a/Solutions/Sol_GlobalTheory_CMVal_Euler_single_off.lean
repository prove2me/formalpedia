-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.single_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:39.22989+00:00
-- url     : https://prove2.me/submissions/ee68e037-4c9c-4352-87c4-d952d8fb672e

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_suppAt_single


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
theorem _root_.solution {v : HeightOneSpectrum (OF E)} {P : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (x : (P.adicCompletion E)ˣ)
    (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ Over w v) : (single P x : Af E) w = 1 :=
  suppAt_single P x w fun h => hw (h ▸ hP)
end GlobalTheory.CMVal.Euler
