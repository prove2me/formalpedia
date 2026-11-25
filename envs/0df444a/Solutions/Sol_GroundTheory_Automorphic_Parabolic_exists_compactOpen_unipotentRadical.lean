-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_compactOpen_unipotentRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:53:06.775134+00:00
-- url     : https://prove2.me/submissions/4e5fe06f-4d47-48db-8f6f-3cabfb86a06b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_unipotentCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_unipotentCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompact_of_bound
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_pow_mul_mem_of_isCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (s : Finset (unipotentRadical F n β)) :
    ∃ K : Subgroup (unipotentRadical F n β), IsCompact (K : Set (unipotentRadical F n β)) ∧
      IsOpen (K : Set (unipotentRadical F n β)) ∧ ∀ x ∈ s, x ∈ K := by
  classical
  let C : Set (GL (Fin n) F) :=
    (fun x : unipotentRadical F n β => (x : GL (Fin n) F)) '' (s : Set _) ∪
      (fun x : unipotentRadical F n β => (x : GL (Fin n) F)⁻¹) '' (s : Set _)
  have hC : IsCompact C :=
    ((s.finite_toSet.image _).union (s.finite_toSet.image _)).isCompact
  obtain ⟨e, he⟩ := exists_pow_mul_mem_of_isCompact F n hC
  refine ⟨unipotentCompact F n β e, isCompact_unipotentCompact e, isOpen_unipotentCompact e,
    fun x hx => mem_unipotentCompact_of_bound (he _ ?_) (he _ ?_)⟩
  · exact Or.inl ⟨x, hx, rfl⟩
  · exact Or.inr ⟨x, hx, rfl⟩
end GroundTheory.Automorphic.Parabolic
