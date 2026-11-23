-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.relIndex_inf_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:20.410114+00:00
-- url     : https://prove2.me/submissions/9b5b942c-8f60-46dc-bfe1-d398e7f15b49

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cosetIncl_injective

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
theorem _root_.solution (hK : K.relIndex K' ≠ 0) :
    (K ⊓ A).relIndex (K' ⊓ A) ≠ 0 := by
  have : (K.subgroupOf K').FiniteIndex := ⟨hK⟩
  have : Finite ((K' ⊓ A : Subgroup G) ⧸ (K ⊓ A).subgroupOf (K' ⊓ A)) :=
    Finite.of_injective _ (cosetIncl_injective (A := A) (K := K) (K' := K'))
  exact Subgroup.index_ne_zero_of_finite
end GroundTheory.Automorphic.Parabolic
