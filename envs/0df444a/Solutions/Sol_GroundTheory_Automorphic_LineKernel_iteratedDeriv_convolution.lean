-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.iteratedDeriv_convolution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:11.162037+00:00
-- url     : https://prove2.me/submissions/430688f9-7608-419a-badd-4d3e09a91b2d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_eq_of_deriv
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_convolution_mul_eq_real
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_iteratedDeriv_of_contDiff
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_iteratedDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {K g : ℝ → ℂ} (hK : LocallyIntegrable K) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (m : ℕ) :
    iteratedDeriv m (K ⋆[mul ℂ ℂ] g) = K ⋆[mul ℂ ℂ] iteratedDeriv m g := by
  have := iteratedDeriv_eq_of_deriv (Φ := fun m => K ⋆[mul ℂ ℂ] iteratedDeriv m g) (fun m => by
    funext x
    rw [convolution_mul_eq_real, convolution_mul_eq_real]
    rw [((hasCompactSupport_iteratedDeriv hgc m).hasDerivAt_convolution_right (mul ℝ ℂ) hK
      ((contDiff_iteratedDeriv_of_contDiff hg m).of_le (by simp)) x).deriv, ← iteratedDeriv_succ]) m
  simpa using this
end GroundTheory.Automorphic.LineKernel
