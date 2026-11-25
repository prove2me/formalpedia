-- Prove2me | solution 1 for GroundTheory.Automorphic.IsHilbertSchmidt.comp_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:25:42.798512+00:00
-- url     : https://prove2.me/submissions/876bd08e-364b-4e54-a512-eeb76fb266b3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_hsNormSq_comp_right_le

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
theorem _root_.solution {T : K →L[𝕜] L} (hT : IsHilbertSchmidt T) (B : H →L[𝕜] K) :
    IsHilbertSchmidt (T.comp B) :=
  (hsNormSq_comp_right_le T B).trans_lt (ENNReal.mul_lt_top (by simp) hT)
end IsHilbertSchmidt
end GroundTheory.Automorphic
