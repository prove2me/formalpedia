-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.locIn_of_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:29.979159+00:00
-- url     : https://prove2.me/submissions/378784c9-96eb-4344-99fa-28cda04736b9

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Theorems.Thm_GlobalTheory_CMVal_Euler_iota_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution {n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E}
    (h : ∀ P, Over P v → Valued.v (z P - 1) ≤ WithZero.exp (-(n : ℤ))) : LocIn n v z :=
  ⟨1, fun P hP => by rw [iota_one]; exact h P hP⟩
end GlobalTheory.CMVal.Euler
