-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.derivOp_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:33.616404+00:00
-- url     : https://prove2.me/submissions/9d14f4bd-9d93-4a4c-8fc5-543f8bdefe12

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_inv_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
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
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {v : E} (hv : h.IsSmoothVector π v) (g : G) (X : 𝔤) :
    h.derivOp π (h.Ad g X) (π g v) = π g (h.derivOp π X v) := by
  have hF : HasFDerivAt (h.expOrbit π v) (fderiv ℝ (h.expOrbit π v) 0) (h.AdL g⁻¹ 0) := by
    simpa using (h.differentiable_expOrbit π hv 0).hasFDerivAt
  have hc := ((π g).restrictScalars ℝ).hasFDerivAt.comp (0 : 𝔤)
    (hF.comp (0 : 𝔤) (h.AdL g⁻¹).hasFDerivAt)
  unfold derivOp
  rw [expOrbit_map]
  have e : (fun Y => π g (h.expOrbit π v (h.Ad g⁻¹ Y))) =
      ((π g).restrictScalars ℝ) ∘ (h.expOrbit π v ∘ h.AdL g⁻¹) := rfl
  rw [e, hc.fderiv]
  simp [Ad_inv_Ad]
end GroundTheory.Automorphic.IsExpLieAlgebra
