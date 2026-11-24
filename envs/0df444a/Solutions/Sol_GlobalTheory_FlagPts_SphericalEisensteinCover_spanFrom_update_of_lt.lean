-- Prove2me | solution 1 for GlobalTheory.FlagPts.SphericalEisensteinCover.spanFrom_update_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:58:16.450614+00:00
-- url     : https://prove2.me/submissions/20b7bde5-d7f7-4cc5-b22f-2eddef6ca2ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
theorem _root_.solution (f : ℕ → W) (N m m' : ℕ) (v : W) (h : m < m') :
    spanFrom k (Function.update f m v) N m' = spanFrom k f N m' := by
  unfold spanFrom
  congr 1
  refine Set.image_congr fun a ha => ?_
  rw [Function.update_of_ne]
  exact (lt_of_lt_of_le h ha.1).ne'
end GlobalTheory.FlagPts.SphericalEisensteinCover
