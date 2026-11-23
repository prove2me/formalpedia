-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.locIn_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:56.847484+00:00
-- url     : https://prove2.me/submissions/b99d1d55-39c2-41e0-83e0-5c6a9e2e6a40

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Theorems.Thm_GlobalTheory_CMVal_Euler_iota_zero
import Theorems.Thm_GlobalTheory_CMVal_Euler_zero_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_LocIn_val_le
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
theorem _root_.solution {v : HeightOneSpectrum (OF E)} {z : Af E} : LocIn 0 v z ↔ ∀ P, Over P v → Valued.v (z P) ≤ 1 :=
  ⟨fun h _ hP => h.val_le hP, fun h => ⟨0, fun P hP => by simpa [iota_zero, zero_coord] using h P hP⟩⟩
end GlobalTheory.CMVal.Euler
