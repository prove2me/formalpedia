-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.mul_mem_MS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:38.165067+00:00
-- url     : https://prove2.me/submissions/7182c913-a356-461e-8313-d27530f0c6db

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_LocIn_mul
import Theorems.Thm_GlobalTheory_CMVal_Euler_mul_coord


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
theorem _root_.solution {m : HeightOneSpectrum (OF E) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 E))} {u y : (Af E)ˣ}
    (hu : ∀ v, LocIn (m v) v (u : Af E)) (hu' : ∀ w, Valued.v ((u : Af E) w) = 1) (hy : y ∈ MS m T) : y * u ∈ MS m T :=
  ⟨fun v => (hy.1 v).mul (hu v), fun w hw => by rw [Units.val_mul, mul_coord, map_mul, hy.2 w hw, hu' w, one_mul]⟩
end GlobalTheory.CMVal.Euler
