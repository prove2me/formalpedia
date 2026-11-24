-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.omega_unifAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:41:41.704348+00:00
-- url     : https://prove2.me/submissions/6fc7f5af-d301-492e-9595-bf3c98c55f6d

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_omega_apply
import Theorems.Thm_GlobalTheory_CMVal_Euler_inv_natCast_cpow
import Theorems.Thm_GlobalTheory_CMVal_finPart_unifAt
import Theorems.Thm_GlobalTheory_CMVal_modF_unifAt


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
theorem _root_.solution (χ : HChar E) (S : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    omega χ S (unifAt w) = (val χ w : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-S) := by
  rw [omega_apply, finPart_unifAt, modF_unifAt, inv_natCast_cpow]
end GlobalTheory.CMVal.Euler
