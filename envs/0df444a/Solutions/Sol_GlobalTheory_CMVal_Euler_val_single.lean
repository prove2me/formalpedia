-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.val_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:14.486384+00:00
-- url     : https://prove2.me/submissions/32a707fa-50a3-4395-9587-86d6489c3a6a

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
theorem _root_.solution {P : HeightOneSpectrum (𝓞 E)} {x : (P.adicCompletion E)ˣ} (hx : Valued.v (x : P.adicCompletion E) = 1)
    (w : HeightOneSpectrum (𝓞 E)) : Valued.v ((single P x : Af E) w) = 1 := by
  by_cases h : w = P
  · subst h; rw [single_self, hx]
  · rw [suppAt_single P x w h, map_one]
end GlobalTheory.CMVal.Euler
