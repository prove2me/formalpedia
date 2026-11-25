-- Prove2me | solution 1 for GroundTheory.LocalField.isCharacter_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:32.29974+00:00
-- url     : https://prove2.me/submissions/bf2c7379-5637-4bce-8112-4610d3e531f9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_isCharacter_zero
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G]
namespace GroundTheory.LocalField
theorem _root_.solution {ι : Type*} (s : Finset ι) {χ : ι → G → ℂ} (h : ∀ i ∈ s, IsCharacter (χ i)) :
    IsCharacter (∑ i ∈ s, χ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCharacter_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
end GroundTheory.LocalField
