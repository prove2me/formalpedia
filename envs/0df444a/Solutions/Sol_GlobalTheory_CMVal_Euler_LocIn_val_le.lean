-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.LocIn.val_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:07.3636+00:00
-- url     : https://prove2.me/submissions/50180955-2595-44b4-bf73-b595bb51863b

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Theorems.Thm_GlobalTheory_CMVal_Euler_val_iota_le_one
import Theorems.Thm_GlobalTheory_CMVal_Euler_LocIn_mono
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
namespace LocIn
theorem _root_.solution {n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E} (h : LocIn n v z) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) : Valued.v (z P) ≤ 1 := by
  obtain ⟨a, ha⟩ := h.mono (Nat.zero_le n)
  have h1 : Valued.v (z P - iota a P) ≤ 1 := by simpa using ha P hP
  have := Valuation.map_add_le _ h1 (val_iota_le_one P a)
  rwa [sub_add_cancel] at this
end LocIn
end GlobalTheory.CMVal.Euler
