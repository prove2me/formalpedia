-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.MS_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:41.059797+00:00
-- url     : https://prove2.me/submissions/6cd163a7-dce5-4b7a-b10a-9d69f4609711

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift

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
theorem _root_.solution (m : HeightOneSpectrum (OF E) → ℕ) {T T' : Finset (HeightOneSpectrum (𝓞 E))} (h : T ⊆ T') : MS m T' ⊆ MS m T :=
  fun _ hy => ⟨hy.1, fun w hw => hy.2 w (h hw)⟩
end GlobalTheory.CMVal.Euler
