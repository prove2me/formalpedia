-- Prove2me | solution 1 for GroundTheory.Automorphic.hasFDerivAt_expSymm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:56.328704+00:00
-- url     : https://prove2.me/submissions/199526e5-5765-47bf-897c-4bcfdbe2ff99

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Theorems.Thm_GroundTheory_Automorphic_expPartialHomeomorph_symm_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
namespace GroundTheory.Automorphic
theorem _root_.solution :
    HasFDerivAt (expPartialHomeomorph ℝ 𝔸).symm (1 : 𝔸 →L[ℝ] 𝔸) 1 := by
  have hd : HasFDerivAt (expPartialHomeomorph ℝ 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸)
      ((expPartialHomeomorph ℝ 𝔸).symm 1) := by
    rw [expPartialHomeomorph_symm_one, coe_expPartialHomeomorph]
    exact (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).congr_fderiv (by ext; simp)
  exact ((expPartialHomeomorph ℝ 𝔸).hasFDerivAt_symm
    (one_mem_expPartialHomeomorph_target ℝ 𝔸) hd).congr_fderiv (by ext; simp)
end GroundTheory.Automorphic
