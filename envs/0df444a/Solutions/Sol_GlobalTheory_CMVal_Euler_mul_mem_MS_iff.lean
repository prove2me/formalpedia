-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.mul_mem_MS_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:21.227865+00:00
-- url     : https://prove2.me/submissions/06551432-9181-4d4b-886e-765613cadbd0

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_mul_mem_MS
import Theorems.Thm_GlobalTheory_CMVal_Euler_val_inv_one
import Theorems.Thm_GlobalTheory_CMVal_Euler_LocIn_inv


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
theorem _root_.solution {m : HeightOneSpectrum (OF E) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 E))} {u : (Af E)ˣ}
    (hu : ∀ v, LocIn (m v) v (u : Af E)) (hu' : ∀ w, Valued.v ((u : Af E) w) = 1) (y : (Af E)ˣ) :
    y * u ∈ MS m T ↔ y ∈ MS m T := by
  refine ⟨fun h => ?_, mul_mem_MS hu hu'⟩
  have := mul_mem_MS (u := u⁻¹) (fun v => (hu v).inv fun P _ => hu' P) (val_inv_one hu') h
  rwa [mul_inv_cancel_right] at this
end GlobalTheory.CMVal.Euler
