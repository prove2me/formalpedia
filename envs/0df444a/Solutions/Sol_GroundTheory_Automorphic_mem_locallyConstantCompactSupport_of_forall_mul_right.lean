-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_locallyConstantCompactSupport_of_forall_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:04.429434+00:00
-- url     : https://prove2.me/submissions/55671d86-4e54-4164-b218-a9b9b5449569

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Theorems.Thm_GroundTheory_Automorphic_apply_eq_of_mem_smul

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
namespace GroundTheory.Automorphic
theorem _root_.solution (K : OpenSubgroup G)
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f ∈ locallyConstantCompactSupport G R E := by
  refine ⟨(IsLocallyConstant.iff_exists_open f).2 fun g => ?_, hf⟩
  refine ⟨g • (K : Set G), K.isOpen.smul g, ?_, fun y hy => apply_eq_of_mem_smul hK hy⟩
  exact Set.mem_smul_set.2 ⟨1, K.one_mem, mul_one g⟩
end GroundTheory.Automorphic
