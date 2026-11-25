-- Prove2me | solution 1 for GlobalTheory.IdxInt.Lin.fine_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:06:49.140273+00:00
-- url     : https://prove2.me/submissions/7af1bf14-e327-4ec9-b6d1-eb271fa69c13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqOfFineSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Lin
variable {W : Type} [AddCommGroup W]
namespace GlobalTheory.IdxInt.Lin
theorem _root_.solution {A B : AddSubgroup W} {φ : W → ℂ} (c : ℂ) (hφ : Fine A φ B) :
    Fine A (fun w => c * φ w) B := by
  refine ⟨hφ.1, hφ.2.1, fun w b hb => by simp [hφ.2.2.1 w b hb], ?_⟩
  refine hφ.2.2.2.subset (Set.image_mono ?_)
  intro w hw h0
  exact hw (by simp [h0])
end GlobalTheory.IdxInt.Lin
