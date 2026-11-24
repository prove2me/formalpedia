-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_forall_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:47.865096+00:00
-- url     : https://prove2.me/submissions/1c031f4e-d79d-40aa-8d11-42e035475aac

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_right

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
theorem _root_.solution {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, ∀ g, f (k * g) = f g := by
  have hf' : (fun g => f g⁻¹) ∈ locallyConstantCompactSupport G R E :=
    ⟨hf.1.comp_continuous continuous_inv, hf.2.comp_homeomorph (Homeomorph.inv G)⟩
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_right hf'
  refine ⟨K, hKc, fun k hk g => ?_⟩
  have := hK g⁻¹ k⁻¹ (inv_mem hk)
  simpa [mul_inv_rev] using this
end GroundTheory.Automorphic
