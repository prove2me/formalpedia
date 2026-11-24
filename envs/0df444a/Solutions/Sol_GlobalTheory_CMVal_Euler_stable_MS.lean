-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.stable_MS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:02:48.307031+00:00
-- url     : https://prove2.me/submissions/59c63aea-249e-4e34-b1b2-24efeae28afa

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_mul_mem_MS_iff
import Theorems.Thm_GlobalTheory_CMVal_Euler_LocIn_mono
import Theorems.Thm_GlobalTheory_CMVal_Euler_locIn_of_mem_hatO
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_val_eq_one


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
theorem _root_.solution {c : Ideal (OF E)} {m : HeightOneSpectrum (OF E) → ℕ} (hm : ∀ v, m v ≤ expIn c v)
    (T : Finset (HeightOneSpectrum (𝓞 E))) : Stable (hatOUnits c) (MS m T) := fun _ hu =>
  mul_mem_MS_iff (fun v => (locIn_of_mem_hatO hu.1 v).mono (hm v)) (OrderUnits.val_eq_one hu)
end GlobalTheory.CMVal.Euler
