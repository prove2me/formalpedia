-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_forall_mul_left_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:55.581008+00:00
-- url     : https://prove2.me/submissions/6ec6cb33-8ac0-4078-9841-3849940a1028

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_right
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_left
import Theorems.Thm_GroundTheory_Automorphic_isCompact_inf_left


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
open Set Filter Topology
open scoped Pointwise
variable {G : Type*} [Group G] {E : Type*}
variable [TopologicalSpace G] [IsTopologicalGroup G] {R : Type*} [Semiring R] [AddCommMonoid E]
  [Module R E]
variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution {f : G → E}
    (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      ∀ k ∈ K, ∀ g, ∀ k' ∈ K, f (k * g * k') = f g := by
  obtain ⟨K₁, h₁, hK₁⟩ := exists_forall_mul_right hf
  obtain ⟨K₂, -, hK₂⟩ := exists_forall_mul_left hf
  refine ⟨K₁ ⊓ K₂, isCompact_inf_left h₁, fun k hk g k' hk' => ?_⟩
  rw [mul_assoc, hK₂ k (OpenSubgroup.mem_inf.1 hk).2, hK₁ g k' (OpenSubgroup.mem_inf.1 hk').1]
end GroundTheory.Automorphic
