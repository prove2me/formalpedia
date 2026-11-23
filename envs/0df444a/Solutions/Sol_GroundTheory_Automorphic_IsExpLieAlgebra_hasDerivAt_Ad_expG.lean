-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_Ad_expG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:55.330801+00:00
-- url     : https://prove2.me/submissions/ddbdfb99-d2c1-45f8-b6b8-2c4c4a468ece

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
include h
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (X Y : 𝔤) :
    HasDerivAt (fun t : ℝ => h.Ad (h.expG (t • X)) Y) (h.bracket X Y) 0 := by
  have hd : HasDerivAt (fun t : ℝ => exp (t • (X : 𝔸)) * Y * exp (t • (-(X : 𝔸))))
      ((X : 𝔸) * Y - Y * X) 0 := by
    have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : 𝔸) (0 : ℝ)).mul_const (Y : 𝔸)).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-(X : 𝔸)) (0 : ℝ))
    simp only [zero_smul, exp_zero, one_mul, mul_one, mul_neg, ← sub_eq_add_neg] at h1
    exact h1
  have hval : ∀ t : ℝ, ((h.Ad (h.expG (t • X)) Y : 𝔤) : 𝔸) =
      exp (t • (X : 𝔸)) * Y * exp (t • (-(X : 𝔸))) := by
    intro t
    show exp (t • (X : 𝔸)) * Y * ↑((expUnit ℝ 𝔸 (t • (X : 𝔸)))⁻¹) = _
    rw [coe_expUnit_inv, smul_neg]
  have key := (subspaceProj 𝔤).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have e : subspaceProj 𝔤 ((X : 𝔸) * Y - Y * X) = h.bracket X Y := by
    rw [← coe_bracket h X Y, subspaceProj_coe]
  rw [e] at key
  refine key.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply]
  rw [← hval t, subspaceProj_coe]
end GroundTheory.Automorphic.IsExpLieAlgebra
