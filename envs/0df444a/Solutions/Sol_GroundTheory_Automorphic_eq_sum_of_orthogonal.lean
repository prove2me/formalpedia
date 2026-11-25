-- Prove2me | solution 1 for GroundTheory.Automorphic.eq_sum_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:18.129792+00:00
-- url     : https://prove2.me/submissions/fd2fe559-17dd-4a34-81b8-20827d212a57

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (B : LinearMap.BilinForm ℝ L)
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ L) (ε : ι → ℝ)
variable {B b ε}
namespace GroundTheory.Automorphic
theorem _root_.solution [DecidableEq ι] (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0) (Y : L) :
    Y = ∑ j, (ε j * B (b j) Y) • b j := by
  conv_lhs => rw [← b.sum_repr Y]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have e : B (b j) Y = b.repr Y j * ε j := by
    have := congrArg (B (b j)) (b.sum_repr Y)
    rw [← this, map_sum]
    simp [horth]
  rw [e, ← mul_assoc, mul_comm (ε j), mul_assoc, hε, mul_one]
end GroundTheory.Automorphic
