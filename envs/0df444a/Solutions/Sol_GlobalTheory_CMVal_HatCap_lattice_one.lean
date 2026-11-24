-- Prove2me | solution 1 for GlobalTheory.CMVal.HatCap.lattice_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:37:05.391215+00:00
-- url     : https://prove2.me/submissions/49033822-b078-44dd-b6c6-b969a229681d

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrder
import Theorems.Thm_GlobalTheory_CMVal_HatCap_mem_orderC_of_mem_hatO
import Theorems.Thm_GlobalTheory_CMVal_algebraMap_mem_hatO


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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.HatCap
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.HatCap
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by
  intro E _ _ _ c hc
  ext x
  rw [mem_lattice, inv_one, Units.val_one, mul_one]
  exact ⟨mem_orderC_of_mem_hatO hc, algebraMap_mem_hatO⟩
end GlobalTheory.CMVal.HatCap
