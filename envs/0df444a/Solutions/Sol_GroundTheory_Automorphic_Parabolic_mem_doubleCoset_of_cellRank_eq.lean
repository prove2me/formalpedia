-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_doubleCoset_of_cellRank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:46:43.500936+00:00
-- url     : https://prove2.me/submissions/eda9fcf9-9e3f-41e5-b1f0-3e0b7c639eb2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_of_mem_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_permGL
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_permGL_mem_doubleCoset_of_card
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_permGL_mem_doubleCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable {β γ : Fin n → ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {g x : GL (Fin n) F}
    (h : ∀ a b, cellRank β γ x a b = cellRank β γ g a b) :
    x ∈ doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) := by
  obtain ⟨w, hw⟩ := exists_permGL_mem_doubleCoset (β := β) (γ := γ) g
  obtain ⟨w', hw'⟩ := exists_permGL_mem_doubleCoset (β := β) (γ := γ) x
  have hcnt : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card := by
    intro a b
    rw [← cellRank_permGL (F := F), ← cellRank_permGL (F := F), ← cellRank_of_mem_doubleCoset hw,
      ← cellRank_of_mem_doubleCoset hw', h]
  have hww' := permGL_mem_doubleCoset_of_card (F := F) hcnt
  rw [doubleCoset_eq_of_mem hw, ← doubleCoset_eq_of_mem hww']
  exact hw'
end GroundTheory.Automorphic.Parabolic
