-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.blockRank_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:32:17.530252+00:00
-- url     : https://prove2.me/submissions/7078798e-307c-48b3-a86e-c1580108b431

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {i j : Fin n} (h : β i < β j) : blockRank β i < blockRank β j := by
  refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans h
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
    simp at this
end GroundTheory.Automorphic.Parabolic
