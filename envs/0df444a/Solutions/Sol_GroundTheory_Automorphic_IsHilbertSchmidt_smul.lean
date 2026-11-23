-- Prove2me | solution 1 for GroundTheory.Automorphic.IsHilbertSchmidt.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:40.926012+00:00
-- url     : https://prove2.me/submissions/c058b939-e4ad-4c1a-87ae-c64ca928edd3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt

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
theorem _root_.solution {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) (c : 𝕜) :
    IsHilbertSchmidt (c • T) :=
  (hilbertSchmidt 𝕜 H K).smul_mem c hT
end IsHilbertSchmidt
end GroundTheory.Automorphic
