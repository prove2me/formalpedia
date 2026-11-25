-- Prove2me | solution 1 for GroundTheory.Global.Artin.extendByZero_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:21.061201+00:00
-- url     : https://prove2.me/submissions/e5b35999-3098-4d14-9e61-916e506a9351

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
theorem _root_.solution {H : Subgroup G} {f : H → ℂ} (hf : IsClassFun f) {h : G} (hh : h ∈ H)
    (g : G) : extendByZero H f (h * g * h⁻¹) = extendByZero H f g := by
  by_cases hg : g ∈ H
  · have hm : h * g * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh)
    rw [extendByZero_of_mem H f hm, extendByZero_of_mem H f hg, ← hf ⟨g, hg⟩ ⟨h, hh⟩]
    rfl
  · have hm : h * g * h⁻¹ ∉ H := fun hm ↦ hg (by
      have := H.mul_mem (H.mul_mem (H.inv_mem hh) hm) hh
      simpa [mul_assoc] using this)
    rw [extendByZero_of_notMem H f hm, extendByZero_of_notMem H f hg]
end GroundTheory.Global.Artin
