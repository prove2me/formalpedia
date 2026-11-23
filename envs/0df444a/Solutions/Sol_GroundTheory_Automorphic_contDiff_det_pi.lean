-- Prove2me | solution 1 for GroundTheory.Automorphic.contDiff_det_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:19.061605+00:00
-- url     : https://prove2.me/submissions/1d06fe2f-d690-4712-abb6-9e47d233d7a6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord

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
theorem _root_.solution {d : ℕ} :
    ContDiff ℝ ∞ (fun f : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => f.det) := by
  have e : (fun f : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => f.det) = fun f =>
      ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, f (Pi.single i 1) (σ i) := by
    funext f
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    congr 1
  rw [e]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  refine contDiff_prod fun i _ => ?_
  exact ((ContinuousLinearMap.proj (σ i) : (Fin d → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ (Fin d → ℝ) (Pi.single i (1 : ℝ) : Fin d → ℝ) :
      ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) →L[ℝ] (Fin d → ℝ))).contDiff
end GroundTheory.Automorphic
