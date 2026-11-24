-- Prove2me | solution 1 for GlobalTheory.T.character_coset_sum_eq_zero_of_subgroup_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:37.947529+00:00
-- url     : https://prove2.me/submissions/37e4a7f5-2f6e-40c7-a733-e721b206cb7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterCosetSumEqZeroOfSubgroupSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterCosetSumEqZeroOfSubgroupSumStatement
import Theorems.Thm_GlobalTheory_BI_char_coset_sum_eq_zero


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
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), IsChar ℂ ℂ χ → ∀ H : Subgroup G, ∑ᶠ u : H, χ u = 0 → ∀ g : G, ∑ᶠ u : H, χ (g * u) = 0 := by
  first | exact @GlobalTheory.BI.char_coset_sum_eq_zero | exact GlobalTheory.BI.char_coset_sum_eq_zero | (intros; apply GlobalTheory.BI.char_coset_sum_eq_zero <;> assumption)
end _root_.GlobalTheory.T
