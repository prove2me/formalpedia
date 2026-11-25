-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:22:56.316818+00:00
-- url     : https://prove2.me/submissions/b3aedabc-d9b4-4d6a-945a-e31400a25ef3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_of_mem_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_doubleCoset_of_cellRank_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_eq_of_le_of_cellHeight_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_setOf_le_cellRank
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
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (β γ : Fin n → ℕ)
variable {β γ}
variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (g : GL (Fin n) F) :
    closure (doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ⊆
      doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) ∪
        {x | cellHeight β γ x < cellHeight β γ g} := by
  set Z := {x : GL (Fin n) F | ∀ a b, cellRank β γ x a b ≤ cellRank β γ g a b}
  have hZ : IsClosed Z := by
    have : Z = ⋂ a, ⋂ b, {x : GL (Fin n) F | cellRank β γ g a b + 1 ≤ cellRank β γ x a b}ᶜ := by
      ext x
      simp only [Z, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, not_le, Nat.lt_succ_iff]
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      (isOpen_setOf_le_cellRank a b _).isClosed_compl
  have hsub : doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) ⊆ Z :=
    fun x hx a b => (cellRank_of_mem_doubleCoset hx a b).le
  intro x hx
  have hxZ : x ∈ Z := closure_minimal hsub hZ hx
  by_cases hlt : cellHeight β γ x < cellHeight β γ g
  · exact Or.inr hlt
  · exact Or.inl (mem_doubleCoset_of_cellRank_eq
      (cellRank_eq_of_le_of_cellHeight_le hxZ (not_lt.1 hlt)))
end GroundTheory.Automorphic.Parabolic
