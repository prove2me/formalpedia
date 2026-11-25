-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.isUnramified_iff_finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:32:31.806902+00:00
-- url     : https://prove2.me/submissions/ee3871a9-ad34-49d5-ba48-8e207655d7d2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField Module
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]
variable {L} (v : NumberField.InfinitePlace K)
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (w : NumberField.InfinitePlace L) [w.LiesOver v] :
    w.IsUnramified K ↔ finrank v.Completion w.Completion = 1 := by
  refine ⟨fun h ↦ h.finrank_eq_one v, fun h ↦ ?_⟩
  rcases w.isUnramified_or_isRamified K with hu | hr
  · exact hu
  · exact absurd (h.symm.trans (hr.finrank_eq_two v)) (by norm_num)
end GroundTheory.Global.InfinitePlace
