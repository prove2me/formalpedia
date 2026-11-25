-- Prove2me | solution 1 for GroundTheory.Automorphic.hasFDerivAt_prodExpCoord_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:53.560345+00:00
-- url     : https://prove2.me/submissions/f03f9993-19d8-40b7-a48e-e8e342de07a4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Theorems.Thm_GroundTheory_Automorphic_prodExpVal_zero
import Theorems.Thm_GroundTheory_Automorphic_hasFDerivAt_prodExpVal_zero
import Theorems.Thm_GroundTheory_Automorphic_hasFDerivAt_expSymm_one
import Theorems.Thm_GroundTheory_Automorphic_logCoord_coe_sum

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
variable {𝔤 : Submodule ℝ 𝔸}
namespace GroundTheory.Automorphic
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    HasFDerivAt (prodExpCoord b)
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
        (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) 0 := by
  have hL : HasFDerivAt (fun w : 𝔸 => b.equivFun.toContinuousLinearEquiv
      (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm w)))
      (((b.equivFun.toContinuousLinearEquiv : 𝔤 →L[ℝ] (Fin d → ℝ)).comp (subspaceProj 𝔤)).comp
        (1 : 𝔸 →L[ℝ] 𝔸)) (prodExpVal (fun i => (b i : 𝔸)) 0) := by
    rw [prodExpVal_zero]
    exact (((b.equivFun.toContinuousLinearEquiv : 𝔤 →L[ℝ] (Fin d → ℝ)).comp
      (subspaceProj 𝔤)).hasFDerivAt).comp (1 : 𝔸) hasFDerivAt_expSymm_one
  refine (hL.comp (0 : Fin d → ℝ) (hasFDerivAt_prodExpVal_zero _)).congr_fderiv ?_
  ext t : 1
  simpa using logCoord_coe_sum b t
end GroundTheory.Automorphic
