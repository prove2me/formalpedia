-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.val_inv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:21:01.618426+00:00
-- url     : https://prove2.me/submissions/0487b57c-6ba9-4528-b0a6-d6eccd67ef54

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_inv_coord


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
theorem _root_.solution {u : (Af E)ˣ} (hu' : ∀ w, Valued.v ((u : Af E) w) = 1) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (((u⁻¹ : (Af E)ˣ) : Af E) w) = 1 := by rw [inv_coord, map_inv₀, hu', inv_one]
end GlobalTheory.CMVal.Euler
