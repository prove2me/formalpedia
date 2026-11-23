-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.mem_aboveF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:07.098372+00:00
-- url     : https://prove2.me/submissions/85bbe265-c366-41a9-9423-984d86eb03a5

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Theorems.Thm_GlobalTheory_CMVal_Euler_over_iff_under

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
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) :
    P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v ↔ Over P v := by
  unfold Formalism.L2.Host.aboveF
  rw [Set.Finite.mem_toFinset, over_iff_under]
  rfl
end GlobalTheory.CMVal.Euler
