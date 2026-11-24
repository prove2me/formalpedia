-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.norm_omega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:38:56.746328+00:00
-- url     : https://prove2.me/submissions/6692a231-9c8b-4dd7-a587-be2dd92aeec2

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_omega_apply
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_modF_pos


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
theorem _root_.solution {χ : HChar E} (h : IsUnitary χ) (S : ℂ) (y : (Af E)ˣ) : ‖omega χ S y‖ = modF y ^ S.re := by
  rw [omega_apply, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (IdeleModule.modF_pos y)]
  have : ‖(finPart χ y : ℂ)‖ = 1 := h _
  rw [this, one_mul]
end GlobalTheory.CMVal.Euler
