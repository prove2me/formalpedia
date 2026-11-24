-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.rank_hom_le_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:19.308806+00:00
-- url     : https://prove2.me/submissions/9a830d12-6069-4f61-8569-d486cab500eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
import Theorems.Thm_GlobalTheory_SemisimpleCount_map_mem_killed
import Theorems.Thm_GlobalTheory_SemisimpleCount_injective_of_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SemisimpleCount
variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
variable {S : Type} [AddCommGroup S] [Module Rg S]
namespace GlobalTheory.SemisimpleCount
theorem _root_.solution [IsSimpleModule Rg S] {s : S} (hs : s ≠ 0) (hI : ∀ x ∈ I, x • s = 0) :
    Module.rank ℂ (S →ₗ[Rg] M) ≤ Module.rank ℂ (killed I M) := by
  refine LinearMap.rank_le_of_injective
    { toFun := fun g => ⟨g s, map_mem_killed I g hI⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl } ?_
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have h0 : a s = 0 := congrArg Subtype.val ha
  exact hs (injective_of_ne_zero h (h0.trans (map_zero a).symm))
end GlobalTheory.SemisimpleCount
