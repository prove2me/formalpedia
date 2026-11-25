-- Prove2me | solution 1 for GroundTheory.Global.Artin.indFun_subtype_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:16:46.736438+00:00
-- url     : https://prove2.me/submissions/87603572-7e50-44a8-900f-a1df456feb25

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_of_mem
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_of_notMem
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
import Theorems.Thm_GroundTheory_GroupCoh_doubleCosetMap_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.doubleCosetMap_mk


attribute [local simp] GroundTheory.Global.Artin.extendByZero_coe

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
namespace GroundTheory.Global.Artin
theorem _root_.solution [Fintype G] (H : Subgroup G) [Fintype H] (f : H → ℂ) (s : G) :
    indFun H.subtype f s = (Nat.card H : ℂ)⁻¹ * ∑ t : G, extendByZero H f (t⁻¹ * s * t) := by
  classical
  rw [indFun_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases hm : t⁻¹ * s * t ∈ H
  · rw [extendByZero_of_mem H f hm, Finset.sum_eq_single ⟨_, hm⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb (Subtype.ext hb')
    · simp
  · rw [extendByZero_of_notMem H f hm]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [if_neg]
    intro hb'
    exact hm (hb' ▸ b.2)
end GroundTheory.Global.Artin
