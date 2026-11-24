-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.MS_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:22:40.824798+00:00
-- url     : https://prove2.me/submissions/c05f1e20-f0a9-408c-80e3-1bdcc05b957e

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_LocIn_val_le
import Theorems.Thm_GlobalTheory_CMVal_Euler_over_under


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
theorem _root_.solution (m : HeightOneSpectrum (OF E) → ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) : MS m T ⊆ intI :=
  fun _ hy w => (hy.1 _).val_le (over_under w)
end GlobalTheory.CMVal.Euler
