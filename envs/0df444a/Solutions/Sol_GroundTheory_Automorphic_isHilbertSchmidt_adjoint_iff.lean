-- Prove2me | solution 1 for GroundTheory.Automorphic.isHilbertSchmidt_adjoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:03:01.037001+00:00
-- url     : https://prove2.me/submissions/94d7c13e-f24c-41df-a3dc-ead1b111eca4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_hsNormSq_adjoint

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
theorem _root_.solution (T : H →L[𝕜] K) :
    IsHilbertSchmidt (T†) ↔ IsHilbertSchmidt T := by
  rw [IsHilbertSchmidt, IsHilbertSchmidt, hsNormSq_adjoint]
end GroundTheory.Automorphic
