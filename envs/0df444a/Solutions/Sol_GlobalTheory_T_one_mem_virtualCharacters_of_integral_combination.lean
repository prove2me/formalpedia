-- Prove2me | solution 1 for GlobalTheory.T.one_mem_virtualCharacters_of_integral_combination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:36:08.818574+00:00
-- url     : https://prove2.me/submissions/d07a785f-c41f-4dc6-ad37-cd485f56beab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemVirtualCharactersOfIntegralCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemVirtualCharactersOfIntegralCombinationStatement
import Theorems.Thm_GlobalTheory_BI_one_mem_of_integral_combination


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (S : AddSubgroup (G → ℂ)), S ≤ Virt ℂ ℂ G → ∀ (ι : Type) [Fintype ι] (r : ι → ℂ) (s : ι → G → ℂ), (∀ i, IsIntegral ℤ (r i)) → (∀ i, s i ∈ S) → (∀ g, ∑ i, r i * s i g = 1) → (1 : G → ℂ) ∈ S := by
  first | exact @GlobalTheory.BI.one_mem_of_integral_combination | exact GlobalTheory.BI.one_mem_of_integral_combination | (intros; apply GlobalTheory.BI.one_mem_of_integral_combination <;> assumption)
end _root_.GlobalTheory.T
