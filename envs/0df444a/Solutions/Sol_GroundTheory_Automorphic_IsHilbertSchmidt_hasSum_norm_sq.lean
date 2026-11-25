-- Prove2me | solution 1 for GroundTheory.Automorphic.IsHilbertSchmidt.hasSum_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:25.426686+00:00
-- url     : https://prove2.me/submissions/87243403-f7ba-4466-b8ef-f2df4b9b33e7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_hsNormSq_eq_tsum
import Theorems.Thm_GroundTheory_Automorphic_hsNorm_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  {L : Type*} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]
namespace GroundTheory.Automorphic
namespace IsHilbertSchmidt
theorem _root_.solution {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 H) : HasSum (fun i => ‖T (b i)‖ ^ 2) (hsNorm T ^ 2) := by
  have hfin : ∑' i, ‖T (b i)‖ₑ ^ 2 ≠ ∞ := by rw [← hsNormSq_eq_tsum b]; exact hT.ne
  have hs := ENNReal.summable_toReal hfin
  rw [hsNorm_sq, hsNormSq_eq_tsum b, ENNReal.tsum_toReal_eq fun i => by simp]
  convert hs.hasSum using 2 with i; simp
end IsHilbertSchmidt
end GroundTheory.Automorphic
