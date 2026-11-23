-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cosetIncl_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:40.231825+00:00
-- url     : https://prove2.me/submissions/1cbbde7b-2413-48a8-bfe3-b24c5f7c6492

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount

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
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {A : Subgroup G}
variable (A) {K K' : Subgroup G}
variable {A}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution : Function.Injective (cosetIncl A (K := K) (K' := K')) := by
  intro r r' hrr'
  unfold cosetIncl at hrr'
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hrr'
  rw [← QuotientGroup.out_eq' r, ← QuotientGroup.out_eq' r', QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · simpa using hrr'
  · have ha := (Subgroup.mem_inf.1 (Quotient.out r).2).2
    have hb := (Subgroup.mem_inf.1 (Quotient.out r').2).2
    simpa using A.mul_mem (A.inv_mem ha) hb
end GroundTheory.Automorphic.Parabolic
