-- Prove2me | solution 1 for GroundTheory.Automorphic.IsHilbertSchmidt.adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:46.933218+00:00
-- url     : https://prove2.me/submissions/059f953c-9b31-4a88-9a88-998bfe1dfcb0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_isHilbertSchmidt_adjoint_iff

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
theorem _root_.solution {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (T†) :=
  (isHilbertSchmidt_adjoint_iff T).2 hT
end IsHilbertSchmidt
end GroundTheory.Automorphic
