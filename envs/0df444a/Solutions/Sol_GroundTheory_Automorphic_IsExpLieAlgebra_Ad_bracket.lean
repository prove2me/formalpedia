-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.Ad_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:33.431875+00:00
-- url     : https://prove2.me/submissions/3a7448a5-694c-4224-b8f0-ef948cae6251

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
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
theorem _root_.solution (g : G) (X Y : 𝔤) :
    h.Ad g (h.bracket X Y) = h.bracket (h.Ad g X) (h.Ad g Y) := by
  have hgi : (((g⁻¹ : G) : 𝔸ˣ) : 𝔸) * ((g : 𝔸ˣ) : 𝔸) = 1 := by
    rw [coe_inv_val, Units.inv_mul]
  apply Subtype.ext
  simp only [coe_Ad, coe_bracket]
  set a := ((g : 𝔸ˣ) : 𝔸)
  set b := (((g⁻¹ : G) : 𝔸ˣ) : 𝔸)
  have e : ∀ U V : 𝔸, a * U * b * (a * V * b) = a * (U * V) * b := by
    intro U V
    calc a * U * b * (a * V * b) = a * U * (b * a) * V * b := by simp only [mul_assoc]
      _ = _ := by rw [hgi, mul_one]; simp only [mul_assoc]
  rw [e, e, mul_sub, sub_mul]
end GroundTheory.Automorphic.IsExpLieAlgebra
