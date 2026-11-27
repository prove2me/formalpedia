-- Prove2me | solution 1 for GlobalTheory.ZM.DwModel.not_denseP_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:46.394107+00:00
-- url     : https://prove2.me/submissions/5eb09cee-f5ee-40b6-9165-2d4c1d72e145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel
namespace GlobalTheory.ZM.DwModel
theorem _root_.solution : ¬ DenseP ({Ideal.span {2}} : Set (Ideal ℤ)) := by
  intro h
  have h2 : (2 : ℤ) = 0 := h 2 fun p hp _ => by
    rw [Set.mem_singleton_iff.mp hp]
    exact Ideal.mem_span_singleton_self 2
  norm_num at h2
end GlobalTheory.ZM.DwModel
