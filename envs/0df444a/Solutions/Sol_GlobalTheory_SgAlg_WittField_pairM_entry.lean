-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.pairM_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:37.732898+00:00
-- url     : https://prove2.me/submissions/e3276329-4f58-4276-a8ea-55134c4c85c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittField
variable {E : Type} [Field E] {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.SgAlg.WittField
theorem _root_.solution {a : ℕ} (X : Matrix (Fin n) (Fin a) E) (i j : Fin a) :
    pairM σ J X X i j = form σ J (fun k => X k j) (fun k => X k i) := by
  simp only [pairM, cT, form, Matrix.mul_apply, mulVec, dotProduct, transpose_apply, map_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring
end GlobalTheory.SgAlg.WittField
